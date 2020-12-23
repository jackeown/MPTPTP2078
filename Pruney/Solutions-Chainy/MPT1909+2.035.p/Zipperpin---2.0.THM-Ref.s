%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kQhLKQ9ULz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 248 expanded)
%              Number of leaves         :   38 (  89 expanded)
%              Depth                    :   20
%              Number of atoms          : 1094 (7278 expanded)
%              Number of equality atoms :   28 ( 203 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k6_domain_1 @ X10 @ X11 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
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

thf('13',plain,(
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
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
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
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
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
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','19','20','21','22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
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

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( v4_tex_2 @ X14 @ X15 )
      | ( X16
       != ( u1_struct_0 @ X14 ) )
      | ( v3_tex_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( v4_tex_2 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k6_domain_1 @ X10 @ X11 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('60',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('69',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('72',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kQhLKQ9ULz
% 0.16/0.36  % Computer   : n017.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 12:16:01 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 92 iterations in 0.064s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.23/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.55  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.23/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.23/0.55  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.23/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.23/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.55  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.55  thf(t77_tex_2, conjecture,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.23/0.55         ( l1_pre_topc @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.23/0.55             ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.55           ( ![C:$i]:
% 0.23/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.55                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.23/0.55                 ( m1_subset_1 @
% 0.23/0.55                   C @ 
% 0.23/0.55                   ( k1_zfmisc_1 @
% 0.23/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.55               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.23/0.55                 ( ![D:$i]:
% 0.23/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.55                     ( ![E:$i]:
% 0.23/0.55                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.55                         ( ( ( D ) = ( E ) ) =>
% 0.23/0.55                           ( ( k8_relset_1 @
% 0.23/0.55                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.23/0.55                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.23/0.55                             ( k2_pre_topc @
% 0.23/0.55                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i]:
% 0.23/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.55            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.55          ( ![B:$i]:
% 0.23/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.23/0.55                ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.55              ( ![C:$i]:
% 0.23/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.55                    ( v1_funct_2 @
% 0.23/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.55                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.23/0.55                    ( m1_subset_1 @
% 0.23/0.55                      C @ 
% 0.23/0.55                      ( k1_zfmisc_1 @
% 0.23/0.55                        ( k2_zfmisc_1 @
% 0.23/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.55                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.23/0.55                    ( ![D:$i]:
% 0.23/0.55                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.55                        ( ![E:$i]:
% 0.23/0.55                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.55                            ( ( ( D ) = ( E ) ) =>
% 0.23/0.55                              ( ( k8_relset_1 @
% 0.23/0.55                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.23/0.55                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.23/0.55                                ( k2_pre_topc @
% 0.23/0.55                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.23/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('2', plain, (((sk_D) = (sk_E))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (![X10 : $i, X11 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X10)
% 0.23/0.55          | ~ (m1_subset_1 @ X11 @ X10)
% 0.23/0.55          | ((k6_domain_1 @ X10 @ X11) = (k1_tarski @ X11)))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.55  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t2_subset, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i]:
% 0.23/0.55         ((r2_hidden @ X3 @ X4)
% 0.23/0.55          | (v1_xboole_0 @ X4)
% 0.23/0.55          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.23/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.55  thf(t63_subset_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r2_hidden @ A @ B ) =>
% 0.23/0.55       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (![X1 : $i, X2 : $i]:
% 0.23/0.55         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.23/0.55          | ~ (r2_hidden @ X1 @ X2))),
% 0.23/0.55      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.23/0.55  thf('10', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.55        (k1_zfmisc_1 @ 
% 0.23/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t76_tex_2, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.23/0.55         ( l1_pre_topc @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.23/0.55             ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.55           ( ![C:$i]:
% 0.23/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.55                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.23/0.55                 ( m1_subset_1 @
% 0.23/0.55                   C @ 
% 0.23/0.55                   ( k1_zfmisc_1 @
% 0.23/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.55               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.23/0.55                 ( ![D:$i]:
% 0.23/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.23/0.55                     ( ![E:$i]:
% 0.23/0.55                       ( ( m1_subset_1 @
% 0.23/0.55                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.55                         ( ( ( D ) = ( E ) ) =>
% 0.23/0.55                           ( ( k8_relset_1 @
% 0.23/0.55                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.23/0.55                               D ) =
% 0.23/0.55                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf('12', plain,
% 0.23/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.55         ((v2_struct_0 @ X19)
% 0.23/0.55          | ~ (v4_tex_2 @ X19 @ X20)
% 0.23/0.55          | ~ (m1_pre_topc @ X19 @ X20)
% 0.23/0.55          | ~ (v3_borsuk_1 @ X21 @ X20 @ X19)
% 0.23/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.55          | ((X22) != (X23))
% 0.23/0.55          | ((k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21 @ 
% 0.23/0.55              X22) = (k2_pre_topc @ X20 @ X23))
% 0.23/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.23/0.55          | ~ (m1_subset_1 @ X21 @ 
% 0.23/0.55               (k1_zfmisc_1 @ 
% 0.23/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.23/0.55          | ~ (v5_pre_topc @ X21 @ X20 @ X19)
% 0.23/0.55          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.23/0.55          | ~ (v1_funct_1 @ X21)
% 0.23/0.55          | ~ (l1_pre_topc @ X20)
% 0.23/0.55          | ~ (v3_tdlat_3 @ X20)
% 0.23/0.55          | ~ (v2_pre_topc @ X20)
% 0.23/0.55          | (v2_struct_0 @ X20))),
% 0.23/0.55      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.23/0.55  thf('13', plain,
% 0.23/0.55      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.23/0.55         ((v2_struct_0 @ X20)
% 0.23/0.55          | ~ (v2_pre_topc @ X20)
% 0.23/0.55          | ~ (v3_tdlat_3 @ X20)
% 0.23/0.55          | ~ (l1_pre_topc @ X20)
% 0.23/0.55          | ~ (v1_funct_1 @ X21)
% 0.23/0.55          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.23/0.55          | ~ (v5_pre_topc @ X21 @ X20 @ X19)
% 0.23/0.55          | ~ (m1_subset_1 @ X21 @ 
% 0.23/0.55               (k1_zfmisc_1 @ 
% 0.23/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.23/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.23/0.55          | ((k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21 @ 
% 0.23/0.55              X23) = (k2_pre_topc @ X20 @ X23))
% 0.23/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.55          | ~ (v3_borsuk_1 @ X21 @ X20 @ X19)
% 0.23/0.55          | ~ (m1_pre_topc @ X19 @ X20)
% 0.23/0.55          | ~ (v4_tex_2 @ X19 @ X20)
% 0.23/0.55          | (v2_struct_0 @ X19))),
% 0.23/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v2_struct_0 @ sk_B)
% 0.23/0.55          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.23/0.55          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.23/0.55          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.23/0.55          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.23/0.55              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.55          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.55               (u1_struct_0 @ sk_B))
% 0.23/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.23/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.55          | ~ (v3_tdlat_3 @ sk_A)
% 0.23/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.55          | (v2_struct_0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['11', '13'])).
% 0.23/0.55  thf('15', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('17', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('18', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('19', plain,
% 0.23/0.55      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('22', plain, ((v3_tdlat_3 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('24', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v2_struct_0 @ sk_B)
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.23/0.55          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.23/0.55              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.55          | (v2_struct_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)],
% 0.23/0.55                ['14', '15', '16', '17', '18', '19', '20', '21', '22', '23'])).
% 0.23/0.55  thf('25', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.55        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.23/0.55            sk_C_1 @ (k1_tarski @ sk_D))
% 0.23/0.55            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.55        | (v2_struct_0 @ sk_B))),
% 0.23/0.55      inference('sup-', [status(thm)], ['10', '24'])).
% 0.23/0.55  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.55  thf(t39_pre_topc, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( l1_pre_topc @ A ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.55           ( ![C:$i]:
% 0.23/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.23/0.55               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf('28', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.55         (~ (m1_pre_topc @ X7 @ X8)
% 0.23/0.55          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.23/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.23/0.55          | ~ (l1_pre_topc @ X8))),
% 0.23/0.55      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.23/0.55  thf('29', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55          | ~ (l1_pre_topc @ X0)
% 0.23/0.55          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.55          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.55  thf('30', plain,
% 0.23/0.55      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('32', plain,
% 0.23/0.55      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.55  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t1_tsep_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( l1_pre_topc @ A ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.55           ( m1_subset_1 @
% 0.23/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.55  thf('34', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         (~ (m1_pre_topc @ X12 @ X13)
% 0.23/0.55          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.23/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.23/0.55          | ~ (l1_pre_topc @ X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.23/0.55  thf('35', plain,
% 0.23/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.23/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.55  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('37', plain,
% 0.23/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.23/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.55  thf(t46_tex_2, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( ( v1_xboole_0 @ B ) & 
% 0.23/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.55           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.23/0.55  thf('38', plain,
% 0.23/0.55      (![X17 : $i, X18 : $i]:
% 0.23/0.55         (~ (v1_xboole_0 @ X17)
% 0.23/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.23/0.55          | ~ (v3_tex_2 @ X17 @ X18)
% 0.23/0.55          | ~ (l1_pre_topc @ X18)
% 0.23/0.55          | ~ (v2_pre_topc @ X18)
% 0.23/0.55          | (v2_struct_0 @ X18))),
% 0.23/0.55      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.23/0.55  thf('39', plain,
% 0.23/0.55      (((v2_struct_0 @ sk_A)
% 0.23/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.55        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.23/0.55        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.23/0.55  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('42', plain,
% 0.23/0.55      (((v2_struct_0 @ sk_A)
% 0.23/0.55        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.23/0.55        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.23/0.55  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('44', plain,
% 0.23/0.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.23/0.55      inference('clc', [status(thm)], ['42', '43'])).
% 0.23/0.55  thf('45', plain,
% 0.23/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.23/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.55  thf(d8_tex_2, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.55           ( ( v4_tex_2 @ B @ A ) <=>
% 0.23/0.55             ( ![C:$i]:
% 0.23/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.55                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf('46', plain,
% 0.23/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.55         (~ (m1_pre_topc @ X14 @ X15)
% 0.23/0.55          | ~ (v4_tex_2 @ X14 @ X15)
% 0.23/0.55          | ((X16) != (u1_struct_0 @ X14))
% 0.23/0.55          | (v3_tex_2 @ X16 @ X15)
% 0.23/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.23/0.55          | ~ (l1_pre_topc @ X15)
% 0.23/0.55          | (v2_struct_0 @ X15))),
% 0.23/0.55      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.23/0.55  thf('47', plain,
% 0.23/0.55      (![X14 : $i, X15 : $i]:
% 0.23/0.55         ((v2_struct_0 @ X15)
% 0.23/0.55          | ~ (l1_pre_topc @ X15)
% 0.23/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.23/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.23/0.55          | (v3_tex_2 @ (u1_struct_0 @ X14) @ X15)
% 0.23/0.55          | ~ (v4_tex_2 @ X14 @ X15)
% 0.23/0.55          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.23/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.23/0.55  thf('48', plain,
% 0.23/0.55      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.23/0.55        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.23/0.55        | (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.23/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.55        | (v2_struct_0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['45', '47'])).
% 0.23/0.55  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('50', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('52', plain,
% 0.23/0.55      (((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.23/0.55  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('54', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.23/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.23/0.55  thf('55', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['44', '54'])).
% 0.23/0.55  thf('56', plain,
% 0.23/0.55      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.55      inference('clc', [status(thm)], ['32', '55'])).
% 0.23/0.55  thf('57', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.23/0.55            sk_C_1 @ (k1_tarski @ sk_D))
% 0.23/0.55            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.55        | (v2_struct_0 @ sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['25', '56'])).
% 0.23/0.55  thf('58', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('59', plain,
% 0.23/0.55      (![X10 : $i, X11 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X10)
% 0.23/0.55          | ~ (m1_subset_1 @ X11 @ X10)
% 0.23/0.55          | ((k6_domain_1 @ X10 @ X11) = (k1_tarski @ X11)))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.55  thf('60', plain,
% 0.23/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.23/0.55  thf('61', plain,
% 0.23/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.23/0.55         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.23/0.55         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('62', plain, (((sk_D) = (sk_E))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('63', plain,
% 0.23/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.23/0.55         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.23/0.55         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.23/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.23/0.55  thf('64', plain,
% 0.23/0.55      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.23/0.55          (k1_tarski @ sk_D))
% 0.23/0.55          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['60', '63'])).
% 0.23/0.55  thf('65', plain,
% 0.23/0.55      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.23/0.55          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.23/0.55        | (v2_struct_0 @ sk_B)
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['57', '64'])).
% 0.23/0.55  thf('66', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | (v2_struct_0 @ sk_B)
% 0.23/0.55        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.23/0.55            != (k2_pre_topc @ sk_A @ 
% 0.23/0.55                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.23/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.23/0.55  thf('67', plain,
% 0.23/0.55      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.23/0.55          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.55        | (v2_struct_0 @ sk_B)
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['5', '66'])).
% 0.23/0.55  thf('68', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | (v2_struct_0 @ sk_B)
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['67'])).
% 0.23/0.55  thf(fc2_struct_0, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.55  thf('69', plain,
% 0.23/0.55      (![X6 : $i]:
% 0.23/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.23/0.55          | ~ (l1_struct_0 @ X6)
% 0.23/0.55          | (v2_struct_0 @ X6))),
% 0.23/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.55  thf('70', plain,
% 0.23/0.55      (((v2_struct_0 @ sk_B)
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.23/0.55  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(dt_l1_pre_topc, axiom,
% 0.23/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.55  thf('72', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.23/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.55  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.23/0.55  thf('74', plain,
% 0.23/0.55      (((v2_struct_0 @ sk_B)
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v2_struct_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['70', '73'])).
% 0.23/0.55  thf('75', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.23/0.55        | (v2_struct_0 @ sk_A)
% 0.23/0.55        | (v2_struct_0 @ sk_B))),
% 0.23/0.55      inference('simplify', [status(thm)], ['74'])).
% 0.23/0.55  thf('76', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['44', '54'])).
% 0.23/0.55  thf('77', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.23/0.55      inference('clc', [status(thm)], ['75', '76'])).
% 0.23/0.55  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.55      inference('clc', [status(thm)], ['77', '78'])).
% 0.23/0.55  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
