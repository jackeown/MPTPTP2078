%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Dg787k8LM

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 204 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          : 1111 (5879 expanded)
%              Number of equality atoms :   29 ( 166 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ X31 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( ( k6_domain_1 @ X38 @ X39 )
        = ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X28 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( v4_tex_2 @ X47 @ X48 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ~ ( v3_borsuk_1 @ X49 @ X48 @ X47 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( X50 != X51 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) @ X49 @ X50 )
        = ( k2_pre_topc @ X48 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) ) ) )
      | ~ ( v5_pre_topc @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v3_tdlat_3 @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('21',plain,(
    ! [X47: $i,X48: $i,X49: $i,X51: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ~ ( v3_tdlat_3 @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) )
      | ~ ( v5_pre_topc @ X49 @ X48 @ X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) @ X49 @ X51 )
        = ( k2_pre_topc @ X48 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v3_borsuk_1 @ X49 @ X48 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ~ ( v4_tex_2 @ X47 @ X48 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26','27','28','29','30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( ( k6_domain_1 @ X38 @ X39 )
        = ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('38',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v3_tex_2 @ X45 @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('65',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ~ ( v4_tex_2 @ X42 @ X43 )
      | ( X44
       != ( u1_struct_0 @ X42 ) )
      | ( v3_tex_2 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('66',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X42 ) @ X43 )
      | ~ ( v4_tex_2 @ X42 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X43 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['58','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Dg787k8LM
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 113 iterations in 0.055s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.22/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(t77_tex_2, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.22/0.51         ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.22/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.51                 ( m1_subset_1 @
% 0.22/0.51                   C @ 
% 0.22/0.51                   ( k1_zfmisc_1 @
% 0.22/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.22/0.51                 ( ![D:$i]:
% 0.22/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                     ( ![E:$i]:
% 0.22/0.51                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.22/0.51                           ( ( k8_relset_1 @
% 0.22/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.51                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.22/0.51                             ( k2_pre_topc @
% 0.22/0.51                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.22/0.51                ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                    ( v1_funct_2 @
% 0.22/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.51                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.51                    ( m1_subset_1 @
% 0.22/0.51                      C @ 
% 0.22/0.51                      ( k1_zfmisc_1 @
% 0.22/0.51                        ( k2_zfmisc_1 @
% 0.22/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.51                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.22/0.51                    ( ![D:$i]:
% 0.22/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                        ( ![E:$i]:
% 0.22/0.51                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.51                            ( ( ( D ) = ( E ) ) =>
% 0.22/0.51                              ( ( k8_relset_1 @
% 0.22/0.51                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.22/0.51                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.22/0.51                                ( k2_pre_topc @
% 0.22/0.51                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.22/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t2_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X30 : $i, X31 : $i]:
% 0.22/0.51         ((r2_hidden @ X30 @ X31)
% 0.22/0.51          | (v1_xboole_0 @ X31)
% 0.22/0.51          | ~ (m1_subset_1 @ X30 @ X31))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('5', plain, (((sk_D) = (sk_E))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X38 : $i, X39 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X38)
% 0.22/0.51          | ~ (m1_subset_1 @ X39 @ X38)
% 0.22/0.51          | ((k6_domain_1 @ X38 @ X39) = (k1_tarski @ X39)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf(t63_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X28 : $i, X29 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (k1_tarski @ X28) @ (k1_zfmisc_1 @ X29))
% 0.22/0.51          | ~ (r2_hidden @ X28 @ X29))),
% 0.22/0.51      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf(t39_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X35 @ X36)
% 0.22/0.51          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.22/0.51          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.22/0.51          | ~ (l1_pre_topc @ X36))),
% 0.22/0.51      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '14'])).
% 0.22/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t76_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.22/0.51         ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.22/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.51                 ( m1_subset_1 @
% 0.22/0.51                   C @ 
% 0.22/0.51                   ( k1_zfmisc_1 @
% 0.22/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.22/0.51                 ( ![D:$i]:
% 0.22/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                     ( ![E:$i]:
% 0.22/0.51                       ( ( m1_subset_1 @
% 0.22/0.51                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.22/0.51                           ( ( k8_relset_1 @
% 0.22/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.51                               D ) =
% 0.22/0.51                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X47)
% 0.22/0.51          | ~ (v4_tex_2 @ X47 @ X48)
% 0.22/0.51          | ~ (m1_pre_topc @ X47 @ X48)
% 0.22/0.51          | ~ (v3_borsuk_1 @ X49 @ X48 @ X47)
% 0.22/0.51          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.22/0.51          | ((X50) != (X51))
% 0.22/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47) @ X49 @ 
% 0.22/0.51              X50) = (k2_pre_topc @ X48 @ X51))
% 0.22/0.51          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.22/0.51          | ~ (m1_subset_1 @ X49 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47))))
% 0.22/0.51          | ~ (v5_pre_topc @ X49 @ X48 @ X47)
% 0.22/0.51          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47))
% 0.22/0.51          | ~ (v1_funct_1 @ X49)
% 0.22/0.51          | ~ (l1_pre_topc @ X48)
% 0.22/0.51          | ~ (v3_tdlat_3 @ X48)
% 0.22/0.51          | ~ (v2_pre_topc @ X48)
% 0.22/0.51          | (v2_struct_0 @ X48))),
% 0.22/0.51      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X47 : $i, X48 : $i, X49 : $i, X51 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X48)
% 0.22/0.51          | ~ (v2_pre_topc @ X48)
% 0.22/0.51          | ~ (v3_tdlat_3 @ X48)
% 0.22/0.51          | ~ (l1_pre_topc @ X48)
% 0.22/0.51          | ~ (v1_funct_1 @ X49)
% 0.22/0.51          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47))
% 0.22/0.51          | ~ (v5_pre_topc @ X49 @ X48 @ X47)
% 0.22/0.51          | ~ (m1_subset_1 @ X49 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47))))
% 0.22/0.51          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.22/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47) @ X49 @ 
% 0.22/0.51              X51) = (k2_pre_topc @ X48 @ X51))
% 0.22/0.51          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.22/0.51          | ~ (v3_borsuk_1 @ X49 @ X48 @ X47)
% 0.22/0.51          | ~ (m1_pre_topc @ X47 @ X48)
% 0.22/0.51          | ~ (v4_tex_2 @ X47 @ X48)
% 0.22/0.51          | (v2_struct_0 @ X47))),
% 0.22/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.51          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 0.22/0.51          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51               (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v3_tdlat_3 @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '21'])).
% 0.22/0.51  thf('23', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('25', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('30', plain, ((v3_tdlat_3 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)],
% 0.22/0.51                ['22', '23', '24', '25', '26', '27', '28', '29', '30', '31'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.22/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.51        | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (v2_struct_0 @ sk_B)
% 0.22/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.22/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '33'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.22/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.51        | (v2_struct_0 @ sk_B)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.51  thf('36', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X38 : $i, X39 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X38)
% 0.22/0.51          | ~ (m1_subset_1 @ X39 @ X38)
% 0.22/0.51          | ((k6_domain_1 @ X38 @ X39) = (k1_tarski @ X39)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.22/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain, (((sk_D) = (sk_E))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.22/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.22/0.51          (k1_tarski @ sk_D))
% 0.22/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.22/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (v2_struct_0 @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '42'])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_B)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.22/0.51            != (k2_pre_topc @ sk_A @ 
% 0.22/0.51                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.22/0.51          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (v2_struct_0 @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '44'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_B)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.51  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t1_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( m1_subset_1 @
% 0.22/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (![X40 : $i, X41 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X40 @ X41)
% 0.22/0.51          | (m1_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.22/0.51          | ~ (l1_pre_topc @ X41))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.51  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf(t5_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X32 @ X33)
% 0.22/0.51          | ~ (v1_xboole_0 @ X34)
% 0.22/0.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | (v2_struct_0 @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['46', '53'])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_B)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '54'])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.51  thf('57', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf(t46_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.51           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (![X45 : $i, X46 : $i]:
% 0.22/0.51         (~ (v1_xboole_0 @ X45)
% 0.22/0.51          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.22/0.51          | ~ (v3_tex_2 @ X45 @ X46)
% 0.22/0.51          | ~ (l1_pre_topc @ X46)
% 0.22/0.51          | ~ (v2_pre_topc @ X46)
% 0.22/0.51          | (v2_struct_0 @ X46))),
% 0.22/0.51      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.22/0.51        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf(d8_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ( v4_tex_2 @ B @ A ) <=>
% 0.22/0.51             ( ![C:$i]:
% 0.22/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X42 @ X43)
% 0.22/0.51          | ~ (v4_tex_2 @ X42 @ X43)
% 0.22/0.51          | ((X44) != (u1_struct_0 @ X42))
% 0.22/0.51          | (v3_tex_2 @ X44 @ X43)
% 0.22/0.51          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.22/0.51          | ~ (l1_pre_topc @ X43)
% 0.22/0.51          | (v2_struct_0 @ X43))),
% 0.22/0.51      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.22/0.51  thf('66', plain,
% 0.22/0.51      (![X42 : $i, X43 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X43)
% 0.22/0.51          | ~ (l1_pre_topc @ X43)
% 0.22/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.22/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.22/0.51          | (v3_tex_2 @ (u1_struct_0 @ X42) @ X43)
% 0.22/0.51          | ~ (v4_tex_2 @ X42 @ X43)
% 0.22/0.51          | ~ (m1_pre_topc @ X42 @ X43))),
% 0.22/0.51      inference('simplify', [status(thm)], ['65'])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.51        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.22/0.51        | (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['64', '66'])).
% 0.22/0.51  thf('68', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('69', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.22/0.51  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('73', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.22/0.51      inference('clc', [status(thm)], ['71', '72'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['61', '62', '63', '73'])).
% 0.22/0.51  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('76', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('clc', [status(thm)], ['74', '75'])).
% 0.22/0.51  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('clc', [status(thm)], ['58', '76'])).
% 0.22/0.51  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
