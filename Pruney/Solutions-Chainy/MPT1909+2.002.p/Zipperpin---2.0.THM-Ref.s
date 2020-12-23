%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yufTwmJstw

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:46 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  196 (1656 expanded)
%              Number of leaves         :   48 ( 487 expanded)
%              Depth                    :   32
%              Number of atoms          : 1631 (52423 expanded)
%              Number of equality atoms :   32 (1513 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X3 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v4_tex_2 @ X33 @ X34 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( v3_borsuk_1 @ X35 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( X36 != X37 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 @ X36 )
        = ( k2_pre_topc @ X34 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v5_pre_topc @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v3_tdlat_3 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( v3_tdlat_3 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v5_pre_topc @ X35 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 @ X37 )
        = ( k2_pre_topc @ X34 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v3_borsuk_1 @ X35 @ X34 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( v4_tex_2 @ X33 @ X34 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
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
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27','28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['57','60'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('62',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('68',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','71','76'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['57','60'])).

thf('80',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_tex_2 @ X31 @ X32 )
      | ( m1_subset_1 @ ( sk_C @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v3_tdlat_3 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v3_tdlat_3 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('89',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc18_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tdlat_3 @ B )
           => ( v3_tdlat_3 @ B ) ) ) ) )).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v3_tdlat_3 @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc18_tex_2])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v3_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v3_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v3_tdlat_3 @ sk_B )
    | ~ ( v1_tdlat_3 @ sk_B ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('97',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v1_tdlat_3 @ X25 )
      | ~ ( v4_tex_2 @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc35_tex_2])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    v3_tdlat_3 @ sk_B ),
    inference(demod,[status(thm)],['95','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('112',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['57','60'])).

thf('114',plain,(
    v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('116',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('119',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('125',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v3_tdlat_3 @ sk_B )
      | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('131',plain,(
    v3_tdlat_3 @ sk_B ),
    inference(demod,[status(thm)],['95','105'])).

thf('132',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['80','81'])).

thf('133',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('134',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_tex_2 @ X31 @ X32 )
      | ( v3_tex_2 @ ( sk_C @ X31 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v3_tdlat_3 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_B ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v3_tdlat_3 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('138',plain,(
    v3_tdlat_3 @ sk_B ),
    inference(demod,[status(thm)],['95','105'])).

thf('139',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('140',plain,
    ( ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    $false ),
    inference('sup-',[status(thm)],['61','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yufTwmJstw
% 0.13/0.36  % Computer   : n002.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:22:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 259 iterations in 0.146s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.58  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.38/0.58  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.38/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.38/0.58  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.58  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.38/0.58  thf(t77_tex_2, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.38/0.58             ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.38/0.58                 ( m1_subset_1 @
% 0.38/0.58                   C @ 
% 0.38/0.58                   ( k1_zfmisc_1 @
% 0.38/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.38/0.58                 ( ![D:$i]:
% 0.38/0.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                     ( ![E:$i]:
% 0.38/0.58                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58                         ( ( ( D ) = ( E ) ) =>
% 0.38/0.58                           ( ( k8_relset_1 @
% 0.38/0.58                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.38/0.58                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.38/0.58                             ( k2_pre_topc @
% 0.38/0.58                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.38/0.58                ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.58              ( ![C:$i]:
% 0.38/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                    ( v1_funct_2 @
% 0.38/0.58                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.38/0.58                    ( m1_subset_1 @
% 0.38/0.58                      C @ 
% 0.38/0.58                      ( k1_zfmisc_1 @
% 0.38/0.58                        ( k2_zfmisc_1 @
% 0.38/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.38/0.58                    ( ![D:$i]:
% 0.38/0.58                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                        ( ![E:$i]:
% 0.38/0.58                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58                            ( ( ( D ) = ( E ) ) =>
% 0.38/0.58                              ( ( k8_relset_1 @
% 0.38/0.58                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.38/0.58                                ( k2_pre_topc @
% 0.38/0.58                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.38/0.58  thf('0', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain, (((sk_D) = (sk_E))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('2', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X19)
% 0.38/0.58          | ~ (m1_subset_1 @ X20 @ X19)
% 0.38/0.58          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.58  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t2_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X7 : $i, X8 : $i]:
% 0.38/0.58         ((r2_hidden @ X7 @ X8)
% 0.38/0.58          | (v1_xboole_0 @ X8)
% 0.38/0.58          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf(t63_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.58       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X3 : $i, X4 : $i]:
% 0.38/0.58         ((m1_subset_1 @ (k1_tarski @ X3) @ (k1_zfmisc_1 @ X4))
% 0.38/0.58          | ~ (r2_hidden @ X3 @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.58  thf(t39_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.58               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X16 @ X17)
% 0.38/0.58          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.58          | ~ (l1_pre_topc @ X17))),
% 0.38/0.58      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '12'])).
% 0.38/0.58  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t76_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.38/0.58             ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.38/0.58                 ( m1_subset_1 @
% 0.38/0.58                   C @ 
% 0.38/0.58                   ( k1_zfmisc_1 @
% 0.38/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.38/0.58                 ( ![D:$i]:
% 0.38/0.58                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.58                     ( ![E:$i]:
% 0.38/0.58                       ( ( m1_subset_1 @
% 0.38/0.58                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58                         ( ( ( D ) = ( E ) ) =>
% 0.38/0.58                           ( ( k8_relset_1 @
% 0.38/0.58                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.38/0.58                               D ) =
% 0.38/0.58                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X33)
% 0.38/0.58          | ~ (v4_tex_2 @ X33 @ X34)
% 0.38/0.58          | ~ (m1_pre_topc @ X33 @ X34)
% 0.38/0.58          | ~ (v3_borsuk_1 @ X35 @ X34 @ X33)
% 0.38/0.58          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.38/0.58          | ((X36) != (X37))
% 0.38/0.58          | ((k8_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35 @ 
% 0.38/0.58              X36) = (k2_pre_topc @ X34 @ X37))
% 0.38/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.38/0.58          | ~ (m1_subset_1 @ X35 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.38/0.58          | ~ (v5_pre_topc @ X35 @ X34 @ X33)
% 0.38/0.58          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.38/0.58          | ~ (v1_funct_1 @ X35)
% 0.38/0.58          | ~ (l1_pre_topc @ X34)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X34)
% 0.38/0.58          | ~ (v2_pre_topc @ X34)
% 0.38/0.58          | (v2_struct_0 @ X34))),
% 0.38/0.58      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X34)
% 0.38/0.58          | ~ (v2_pre_topc @ X34)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X34)
% 0.38/0.58          | ~ (l1_pre_topc @ X34)
% 0.38/0.58          | ~ (v1_funct_1 @ X35)
% 0.38/0.58          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.38/0.58          | ~ (v5_pre_topc @ X35 @ X34 @ X33)
% 0.38/0.58          | ~ (m1_subset_1 @ X35 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.38/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.38/0.58          | ((k8_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35 @ 
% 0.38/0.58              X37) = (k2_pre_topc @ X34 @ X37))
% 0.38/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.38/0.58          | ~ (v3_borsuk_1 @ X35 @ X34 @ X33)
% 0.38/0.58          | ~ (m1_pre_topc @ X33 @ X34)
% 0.38/0.58          | ~ (v4_tex_2 @ X33 @ X34)
% 0.38/0.58          | (v2_struct_0 @ X33))),
% 0.38/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.38/0.58          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | ~ (v3_tdlat_3 @ sk_A)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '19'])).
% 0.38/0.58  thf('21', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('23', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('24', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('26', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('28', plain, ((v3_tdlat_3 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['20', '21', '22', '23', '24', '25', '26', '27', '28', '29'])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_C_1 @ (k1_tarski @ sk_D))
% 0.38/0.58            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['16', '30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_C_1 @ (k1_tarski @ sk_D))
% 0.38/0.58            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['15', '31'])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_C_1 @ (k1_tarski @ sk_D))
% 0.38/0.58            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.58  thf('34', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X19)
% 0.38/0.58          | ~ (m1_subset_1 @ X20 @ X19)
% 0.38/0.58          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.38/0.58         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.38/0.58         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('38', plain, (((sk_D) = (sk_E))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.38/0.58         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.38/0.58         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.38/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.38/0.58          (k1_tarski @ sk_D))
% 0.38/0.58          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '39'])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.38/0.58          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['33', '40'])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.38/0.58            != (k2_pre_topc @ sk_A @ 
% 0.38/0.58                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.38/0.58      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.38/0.58          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '42'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.58  thf('45', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t1_tsep_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( m1_subset_1 @
% 0.38/0.58             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X21 : $i, X22 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X21 @ X22)
% 0.38/0.58          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.58          | ~ (l1_pre_topc @ X22))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.58  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.58  thf(cc1_subset_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.38/0.58          | (v1_xboole_0 @ X5)
% 0.38/0.58          | ~ (v1_xboole_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['44', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.38/0.58  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('clc', [status(thm)], ['53', '54'])).
% 0.38/0.58  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('57', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.58  thf('58', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.58  thf(l13_xboole_0, axiom,
% 0.38/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.58  thf('60', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['57', '60'])).
% 0.38/0.58  thf(t4_subset_1, axiom,
% 0.38/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf('63', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf(t35_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( v1_xboole_0 @ B ) & 
% 0.38/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.58           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (![X27 : $i, X28 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ X27)
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.38/0.58          | (v2_tex_2 @ X27 @ X28)
% 0.38/0.58          | ~ (l1_pre_topc @ X28)
% 0.38/0.58          | ~ (v2_pre_topc @ X28)
% 0.38/0.58          | (v2_struct_0 @ X28))),
% 0.38/0.58      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_tex_2 @ X0 @ sk_B)
% 0.38/0.58          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.58  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.58          | (v2_pre_topc @ X12)
% 0.38/0.58          | ~ (l1_pre_topc @ X13)
% 0.38/0.58          | ~ (v2_pre_topc @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.58  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.38/0.58  thf('72', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_m1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X14 @ X15)
% 0.38/0.58          | (l1_pre_topc @ X14)
% 0.38/0.58          | ~ (l1_pre_topc @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.58  thf('74', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.58  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.38/0.58  thf('77', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_tex_2 @ X0 @ sk_B)
% 0.38/0.58          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['65', '71', '76'])).
% 0.38/0.58  thf('78', plain,
% 0.38/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.58        | (v2_tex_2 @ k1_xboole_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['62', '77'])).
% 0.38/0.58  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['57', '60'])).
% 0.38/0.58  thf('80', plain, (((v2_tex_2 @ k1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['78', '79'])).
% 0.38/0.58  thf('81', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('82', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_B)),
% 0.38/0.58      inference('clc', [status(thm)], ['80', '81'])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf(t65_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.58                ( ![C:$i]:
% 0.38/0.58                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('84', plain,
% 0.38/0.58      (![X31 : $i, X32 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.38/0.58          | ~ (v2_tex_2 @ X31 @ X32)
% 0.38/0.58          | (m1_subset_1 @ (sk_C @ X31 @ X32) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.38/0.58          | ~ (l1_pre_topc @ X32)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X32)
% 0.38/0.58          | ~ (v2_pre_topc @ X32)
% 0.38/0.58          | (v2_struct_0 @ X32))),
% 0.38/0.58      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      (((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_B) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58        | ~ (v3_tdlat_3 @ sk_B)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['82', '85'])).
% 0.38/0.58  thf('87', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.38/0.58  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc18_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( ( v1_tdlat_3 @ B ) => ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.38/0.58  thf('90', plain,
% 0.38/0.58      (![X23 : $i, X24 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X23 @ X24)
% 0.38/0.58          | (v3_tdlat_3 @ X23)
% 0.38/0.58          | ~ (v1_tdlat_3 @ X23)
% 0.38/0.58          | ~ (l1_pre_topc @ X24)
% 0.38/0.58          | (v2_struct_0 @ X24))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc18_tex_2])).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | ~ (v1_tdlat_3 @ sk_B)
% 0.38/0.58        | (v3_tdlat_3 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.58  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('93', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A) | ~ (v1_tdlat_3 @ sk_B) | (v3_tdlat_3 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['91', '92'])).
% 0.38/0.58  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('95', plain, (((v3_tdlat_3 @ sk_B) | ~ (v1_tdlat_3 @ sk_B))),
% 0.38/0.58      inference('clc', [status(thm)], ['93', '94'])).
% 0.38/0.58  thf('96', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc35_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) ) =>
% 0.38/0.58             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) ) ) ) ) ))).
% 0.38/0.58  thf('97', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X25 @ X26)
% 0.38/0.58          | (v1_tdlat_3 @ X25)
% 0.38/0.58          | ~ (v4_tex_2 @ X25 @ X26)
% 0.38/0.58          | (v2_struct_0 @ X25)
% 0.38/0.58          | ~ (l1_pre_topc @ X26)
% 0.38/0.58          | (v2_struct_0 @ X26))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc35_tex_2])).
% 0.38/0.58  thf('98', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.38/0.58        | (v1_tdlat_3 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.38/0.58  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('100', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('101', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v1_tdlat_3 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.38/0.58  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('103', plain, (((v1_tdlat_3 @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('clc', [status(thm)], ['101', '102'])).
% 0.38/0.58  thf('104', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('105', plain, ((v1_tdlat_3 @ sk_B)),
% 0.38/0.58      inference('clc', [status(thm)], ['103', '104'])).
% 0.38/0.58  thf('106', plain, ((v3_tdlat_3 @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['95', '105'])).
% 0.38/0.58  thf('107', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.38/0.58  thf('108', plain,
% 0.38/0.58      (((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_B) @ 
% 0.38/0.58         (k1_zfmisc_1 @ k1_xboole_0))
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['86', '87', '88', '106', '107'])).
% 0.38/0.58  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('110', plain,
% 0.38/0.58      ((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_B) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.38/0.58      inference('clc', [status(thm)], ['108', '109'])).
% 0.38/0.58  thf('111', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.38/0.58          | (v1_xboole_0 @ X5)
% 0.38/0.58          | ~ (v1_xboole_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.58  thf('112', plain,
% 0.38/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.58        | (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['110', '111'])).
% 0.38/0.58  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['57', '60'])).
% 0.38/0.58  thf('114', plain, ((v1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['112', '113'])).
% 0.38/0.58  thf('115', plain,
% 0.38/0.58      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf('116', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.38/0.58          | (v1_xboole_0 @ X5)
% 0.38/0.58          | ~ (v1_xboole_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.58  thf('117', plain,
% 0.38/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['115', '116'])).
% 0.38/0.58  thf('118', plain,
% 0.38/0.58      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf('119', plain,
% 0.38/0.58      (![X27 : $i, X28 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ X27)
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.38/0.58          | (v2_tex_2 @ X27 @ X28)
% 0.38/0.58          | ~ (l1_pre_topc @ X28)
% 0.38/0.58          | ~ (v2_pre_topc @ X28)
% 0.38/0.58          | (v2_struct_0 @ X28))),
% 0.38/0.58      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.38/0.58  thf('120', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.58          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['118', '119'])).
% 0.38/0.58  thf('121', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ X1)
% 0.38/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['117', '120'])).
% 0.38/0.58  thf('122', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.58  thf('123', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v1_xboole_0 @ X1)
% 0.38/0.58          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['121', '122'])).
% 0.38/0.58  thf('124', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v3_tdlat_3 @ X0)
% 0.38/0.58          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (v1_xboole_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['123'])).
% 0.38/0.58  thf(t46_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( v1_xboole_0 @ B ) & 
% 0.38/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.58           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.38/0.58  thf('125', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.38/0.58          | ~ (v3_tex_2 @ X29 @ X30)
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.38/0.58  thf('126', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v1_xboole_0 @ X1)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.38/0.58          | ~ (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.58  thf('127', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.38/0.58          | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.58          | ~ (v1_xboole_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['126'])).
% 0.38/0.58  thf('128', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | ~ (v1_xboole_0 @ X0)
% 0.38/0.58          | ~ (v3_tdlat_3 @ sk_B)
% 0.38/0.58          | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_B) @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['114', '127'])).
% 0.38/0.58  thf('129', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.38/0.58  thf('130', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.38/0.58  thf('131', plain, ((v3_tdlat_3 @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['95', '105'])).
% 0.38/0.58  thf('132', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_B)),
% 0.38/0.58      inference('clc', [status(thm)], ['80', '81'])).
% 0.38/0.58  thf('133', plain,
% 0.38/0.58      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf('134', plain,
% 0.38/0.58      (![X31 : $i, X32 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.38/0.58          | ~ (v2_tex_2 @ X31 @ X32)
% 0.38/0.58          | (v3_tex_2 @ (sk_C @ X31 @ X32) @ X32)
% 0.38/0.58          | ~ (l1_pre_topc @ X32)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X32)
% 0.38/0.58          | ~ (v2_pre_topc @ X32)
% 0.38/0.58          | (v2_struct_0 @ X32))),
% 0.38/0.58      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.38/0.58  thf('135', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.38/0.58          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['133', '134'])).
% 0.38/0.58  thf('136', plain,
% 0.38/0.58      (((v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_B) @ sk_B)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58        | ~ (v3_tdlat_3 @ sk_B)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['132', '135'])).
% 0.38/0.58  thf('137', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.38/0.58  thf('138', plain, ((v3_tdlat_3 @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['95', '105'])).
% 0.38/0.58  thf('139', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.38/0.58  thf('140', plain,
% 0.38/0.58      (((v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_B) @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 0.38/0.58  thf('141', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('142', plain, ((v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_B) @ sk_B)),
% 0.38/0.58      inference('clc', [status(thm)], ['140', '141'])).
% 0.38/0.58  thf('143', plain,
% 0.38/0.58      (![X0 : $i]: ((v2_struct_0 @ sk_B) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['128', '129', '130', '131', '142'])).
% 0.38/0.58  thf('144', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('145', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.38/0.58      inference('clc', [status(thm)], ['143', '144'])).
% 0.38/0.58  thf('146', plain, ($false), inference('sup-', [status(thm)], ['61', '145'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
