%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfSsHuCGHW

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:50 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 261 expanded)
%              Number of leaves         :   37 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          : 1122 (7633 expanded)
%              Number of equality atoms :   28 ( 211 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( ( k6_domain_1 @ X41 @ X42 )
        = ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X34 ) @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('12',plain,(
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

thf('13',plain,(
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
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','19','20','21','22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_tex_2 @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

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

thf('46',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ~ ( v4_tex_2 @ X45 @ X46 )
      | ( X47
       != ( u1_struct_0 @ X45 ) )
      | ( v3_tex_2 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('47',plain,(
    ! [X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X45 ) @ X46 )
      | ~ ( v4_tex_2 @ X45 @ X46 )
      | ~ ( m1_pre_topc @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( ( k6_domain_1 @ X41 @ X42 )
        = ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('60',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('70',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('71',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfSsHuCGHW
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 212 iterations in 0.122s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.57  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.39/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.57  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.39/0.57  thf(t77_tex_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.39/0.57         ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.39/0.57             ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.39/0.57                 ( m1_subset_1 @
% 0.39/0.57                   C @ 
% 0.39/0.57                   ( k1_zfmisc_1 @
% 0.39/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.39/0.57                 ( ![D:$i]:
% 0.39/0.57                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.39/0.57                     ( ![E:$i]:
% 0.39/0.57                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57                         ( ( ( D ) = ( E ) ) =>
% 0.39/0.57                           ( ( k8_relset_1 @
% 0.39/0.57                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.39/0.57                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.39/0.57                             ( k2_pre_topc @
% 0.39/0.57                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.57            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.39/0.57                ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.57              ( ![C:$i]:
% 0.39/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.57                    ( v1_funct_2 @
% 0.39/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.39/0.57                    ( m1_subset_1 @
% 0.39/0.57                      C @ 
% 0.39/0.57                      ( k1_zfmisc_1 @
% 0.39/0.57                        ( k2_zfmisc_1 @
% 0.39/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.39/0.57                    ( ![D:$i]:
% 0.39/0.57                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.39/0.57                        ( ![E:$i]:
% 0.39/0.57                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57                            ( ( ( D ) = ( E ) ) =>
% 0.39/0.57                              ( ( k8_relset_1 @
% 0.39/0.57                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.57                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.39/0.57                                ( k2_pre_topc @
% 0.39/0.57                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.39/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('2', plain, (((sk_D) = (sk_E))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.57       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X41 : $i, X42 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X41)
% 0.39/0.57          | ~ (m1_subset_1 @ X42 @ X41)
% 0.39/0.57          | ((k6_domain_1 @ X41 @ X42) = (k1_tarski @ X42)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t2_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X36 : $i, X37 : $i]:
% 0.39/0.57         ((r2_hidden @ X36 @ X37)
% 0.39/0.57          | (v1_xboole_0 @ X37)
% 0.39/0.57          | ~ (m1_subset_1 @ X36 @ X37))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.57        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(t63_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X34 : $i, X35 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_tarski @ X34) @ (k1_zfmisc_1 @ X35))
% 0.39/0.57          | ~ (r2_hidden @ X34 @ X35))),
% 0.39/0.57      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.57        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t76_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.39/0.57         ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.39/0.57             ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.39/0.57                 ( m1_subset_1 @
% 0.39/0.57                   C @ 
% 0.39/0.57                   ( k1_zfmisc_1 @
% 0.39/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.39/0.57                 ( ![D:$i]:
% 0.39/0.57                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.57                     ( ![E:$i]:
% 0.39/0.57                       ( ( m1_subset_1 @
% 0.39/0.57                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                         ( ( ( D ) = ( E ) ) =>
% 0.39/0.57                           ( ( k8_relset_1 @
% 0.39/0.57                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.39/0.57                               D ) =
% 0.39/0.57                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X50)
% 0.39/0.57          | ~ (v4_tex_2 @ X50 @ X51)
% 0.39/0.57          | ~ (m1_pre_topc @ X50 @ X51)
% 0.39/0.57          | ~ (v3_borsuk_1 @ X52 @ X51 @ X50)
% 0.39/0.57          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.39/0.57          | ((X53) != (X54))
% 0.39/0.57          | ((k8_relset_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50) @ X52 @ 
% 0.39/0.57              X53) = (k2_pre_topc @ X51 @ X54))
% 0.39/0.57          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.39/0.57          | ~ (m1_subset_1 @ X52 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))))
% 0.39/0.57          | ~ (v5_pre_topc @ X52 @ X51 @ X50)
% 0.39/0.57          | ~ (v1_funct_2 @ X52 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))
% 0.39/0.57          | ~ (v1_funct_1 @ X52)
% 0.39/0.57          | ~ (l1_pre_topc @ X51)
% 0.39/0.57          | ~ (v3_tdlat_3 @ X51)
% 0.39/0.57          | ~ (v2_pre_topc @ X51)
% 0.39/0.57          | (v2_struct_0 @ X51))),
% 0.39/0.57      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X50 : $i, X51 : $i, X52 : $i, X54 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X51)
% 0.39/0.57          | ~ (v2_pre_topc @ X51)
% 0.39/0.57          | ~ (v3_tdlat_3 @ X51)
% 0.39/0.57          | ~ (l1_pre_topc @ X51)
% 0.39/0.57          | ~ (v1_funct_1 @ X52)
% 0.39/0.57          | ~ (v1_funct_2 @ X52 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))
% 0.39/0.57          | ~ (v5_pre_topc @ X52 @ X51 @ X50)
% 0.39/0.57          | ~ (m1_subset_1 @ X52 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))))
% 0.39/0.57          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.39/0.57          | ((k8_relset_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50) @ X52 @ 
% 0.39/0.57              X54) = (k2_pre_topc @ X51 @ X54))
% 0.39/0.57          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.39/0.57          | ~ (v3_borsuk_1 @ X52 @ X51 @ X50)
% 0.39/0.57          | ~ (m1_pre_topc @ X50 @ X51)
% 0.39/0.57          | ~ (v4_tex_2 @ X50 @ X51)
% 0.39/0.57          | (v2_struct_0 @ X50))),
% 0.39/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B_1)
% 0.39/0.57          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.39/0.57          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.39/0.57          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B_1))
% 0.39/0.57          | ~ (v1_funct_1 @ sk_C_1)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | ~ (v3_tdlat_3 @ sk_A)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57          | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['11', '13'])).
% 0.39/0.57  thf('15', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('16', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('17', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('18', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('22', plain, ((v3_tdlat_3 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B_1)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.39/0.57          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)],
% 0.39/0.57                ['14', '15', '16', '17', '18', '19', '20', '21', '22', '23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57            sk_C_1 @ (k1_tarski @ sk_D))
% 0.39/0.57            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.39/0.57        | (v2_struct_0 @ sk_B_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['10', '24'])).
% 0.39/0.57  thf('26', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.57        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf(t39_pre_topc, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.57               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X38 @ X39)
% 0.39/0.57          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.39/0.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.39/0.57          | ~ (l1_pre_topc @ X39))),
% 0.39/0.57      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.57          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.39/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['26', '29'])).
% 0.39/0.57  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.39/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('33', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t1_tsep_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.57           ( m1_subset_1 @
% 0.39/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X43 : $i, X44 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X43 @ X44)
% 0.39/0.57          | (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.39/0.57          | ~ (l1_pre_topc @ X44))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf(t46_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.57             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X48 : $i, X49 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X48)
% 0.39/0.57          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.39/0.57          | ~ (v3_tex_2 @ X48 @ X49)
% 0.39/0.57          | ~ (l1_pre_topc @ X49)
% 0.39/0.57          | ~ (v2_pre_topc @ X49)
% 0.39/0.57          | (v2_struct_0 @ X49))),
% 0.39/0.57      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_A)
% 0.39/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.39/0.57        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_A)
% 0.39/0.57        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.39/0.57        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.39/0.57  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.57        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.39/0.57      inference('clc', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf(d8_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.57           ( ( v4_tex_2 @ B @ A ) <=>
% 0.39/0.57             ( ![C:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X45 @ X46)
% 0.39/0.57          | ~ (v4_tex_2 @ X45 @ X46)
% 0.39/0.57          | ((X47) != (u1_struct_0 @ X45))
% 0.39/0.57          | (v3_tex_2 @ X47 @ X46)
% 0.39/0.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.39/0.57          | ~ (l1_pre_topc @ X46)
% 0.39/0.57          | (v2_struct_0 @ X46))),
% 0.39/0.57      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (![X45 : $i, X46 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X46)
% 0.39/0.57          | ~ (l1_pre_topc @ X46)
% 0.39/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.39/0.57          | (v3_tex_2 @ (u1_struct_0 @ X45) @ X46)
% 0.39/0.57          | ~ (v4_tex_2 @ X45 @ X46)
% 0.39/0.57          | ~ (m1_pre_topc @ X45 @ X46))),
% 0.39/0.57      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.39/0.57        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.39/0.57        | (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['45', '47'])).
% 0.39/0.57  thf('49', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('50', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.39/0.57  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('54', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.39/0.57      inference('clc', [status(thm)], ['52', '53'])).
% 0.39/0.57  thf('55', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '54'])).
% 0.39/0.57  thf('56', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('clc', [status(thm)], ['32', '55'])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57            sk_C_1 @ (k1_tarski @ sk_D))
% 0.39/0.57            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.39/0.57        | (v2_struct_0 @ sk_B_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['25', '56'])).
% 0.39/0.57  thf('58', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('59', plain,
% 0.39/0.57      (![X41 : $i, X42 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X41)
% 0.39/0.57          | ~ (m1_subset_1 @ X42 @ X41)
% 0.39/0.57          | ((k6_domain_1 @ X41 @ X42) = (k1_tarski @ X42)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.57  thf('60', plain,
% 0.39/0.57      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.57  thf('61', plain,
% 0.39/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.57         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.39/0.57         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('62', plain, (((sk_D) = (sk_E))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.58         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.39/0.58         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.39/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.39/0.58  thf('64', plain,
% 0.39/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.58          sk_C_1 @ (k1_tarski @ sk_D))
% 0.39/0.58          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['60', '63'])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.39/0.58          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.39/0.58        | (v2_struct_0 @ sk_B_1)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['57', '64'])).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_B_1)
% 0.39/0.58        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.39/0.58            != (k2_pre_topc @ sk_A @ 
% 0.39/0.58                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['65'])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.39/0.58          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v2_struct_0 @ sk_B_1)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '66'])).
% 0.39/0.58  thf('68', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_B_1)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf('70', plain,
% 0.39/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf(l3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.58  thf('71', plain,
% 0.39/0.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X31 @ X32)
% 0.39/0.58          | (r2_hidden @ X31 @ X33)
% 0.39/0.58          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.39/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.58  thf('72', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['69', '72'])).
% 0.39/0.58  thf(d1_xboole_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.58  thf('76', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B_1)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['68', '75'])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_B_1))),
% 0.39/0.58      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.58  thf('78', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['44', '54'])).
% 0.39/0.58  thf('79', plain, (((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('80', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('81', plain, ((v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('clc', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('82', plain, ($false), inference('demod', [status(thm)], ['0', '81'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
