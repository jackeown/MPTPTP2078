%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2zcOd0zIj7

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:48 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 249 expanded)
%              Number of leaves         :   37 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          : 1203 (7350 expanded)
%              Number of equality atoms :   27 ( 206 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X19 @ ( k1_connsp_2 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('5',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['2','8','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X19 @ ( k1_connsp_2 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_A @ sk_D ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_tex_2 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v3_borsuk_1 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X24 != X25 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ X23 @ X24 )
        = ( k2_pre_topc @ X22 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v5_pre_topc @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v3_tdlat_3 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( v3_tdlat_3 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v5_pre_topc @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ X23 @ X25 )
        = ( k2_pre_topc @ X22 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_borsuk_1 @ X23 @ X22 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v4_tex_2 @ X21 @ X22 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60','61','62','63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('71',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','95'])).

thf('97',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2zcOd0zIj7
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:37:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 96 iterations in 0.056s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.34/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.34/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.34/0.52  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.34/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.34/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.34/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.52  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.34/0.52  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.52  thf(t77_tex_2, conjecture,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.34/0.52         ( l1_pre_topc @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.34/0.52             ( m1_pre_topc @ B @ A ) ) =>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.34/0.52                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.34/0.52                 ( m1_subset_1 @
% 0.34/0.52                   C @ 
% 0.34/0.52                   ( k1_zfmisc_1 @
% 0.34/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.34/0.52               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.34/0.52                 ( ![D:$i]:
% 0.34/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.34/0.52                     ( ![E:$i]:
% 0.34/0.52                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.52                         ( ( ( D ) = ( E ) ) =>
% 0.34/0.52                           ( ( k8_relset_1 @
% 0.34/0.52                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.34/0.52                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.34/0.52                             ( k2_pre_topc @
% 0.34/0.52                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]:
% 0.34/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.34/0.52            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.52          ( ![B:$i]:
% 0.34/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.34/0.52                ( m1_pre_topc @ B @ A ) ) =>
% 0.34/0.52              ( ![C:$i]:
% 0.34/0.52                ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.52                    ( v1_funct_2 @
% 0.34/0.52                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.34/0.52                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.34/0.52                    ( m1_subset_1 @
% 0.34/0.52                      C @ 
% 0.34/0.52                      ( k1_zfmisc_1 @
% 0.34/0.52                        ( k2_zfmisc_1 @
% 0.34/0.52                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.34/0.52                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.34/0.52                    ( ![D:$i]:
% 0.34/0.52                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.34/0.52                        ( ![E:$i]:
% 0.34/0.52                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.52                            ( ( ( D ) = ( E ) ) =>
% 0.34/0.52                              ( ( k8_relset_1 @
% 0.34/0.52                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.34/0.52                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.34/0.52                                ( k2_pre_topc @
% 0.34/0.52                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.34/0.52  thf('0', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t30_connsp_2, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.52           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X19 : $i, X20 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.34/0.52          | (r2_hidden @ X19 @ (k1_connsp_2 @ X20 @ X19))
% 0.34/0.52          | ~ (l1_pre_topc @ X20)
% 0.34/0.52          | ~ (v2_pre_topc @ X20)
% 0.34/0.52          | (v2_struct_0 @ X20))),
% 0.34/0.52      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (((v2_struct_0 @ sk_B)
% 0.34/0.52        | ~ (v2_pre_topc @ sk_B)
% 0.34/0.52        | ~ (l1_pre_topc @ sk_B)
% 0.34/0.52        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.52  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc1_pre_topc, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X8 : $i, X9 : $i]:
% 0.34/0.52         (~ (m1_pre_topc @ X8 @ X9)
% 0.34/0.52          | (v2_pre_topc @ X8)
% 0.34/0.52          | ~ (l1_pre_topc @ X9)
% 0.34/0.52          | ~ (v2_pre_topc @ X9))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.52  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.34/0.52  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(dt_m1_pre_topc, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i]:
% 0.34/0.52         (~ (m1_pre_topc @ X10 @ X11)
% 0.34/0.52          | (l1_pre_topc @ X10)
% 0.34/0.52          | ~ (l1_pre_topc @ X11))),
% 0.34/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.34/0.52  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (((v2_struct_0 @ sk_B) | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.34/0.52      inference('demod', [status(thm)], ['2', '8', '13'])).
% 0.34/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('16', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D))),
% 0.34/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.34/0.52  thf('17', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(dt_k1_connsp_2, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.34/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52       ( m1_subset_1 @
% 0.34/0.52         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (![X17 : $i, X18 : $i]:
% 0.34/0.52         (~ (l1_pre_topc @ X17)
% 0.34/0.52          | ~ (v2_pre_topc @ X17)
% 0.34/0.52          | (v2_struct_0 @ X17)
% 0.34/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.34/0.52          | (m1_subset_1 @ (k1_connsp_2 @ X17 @ X18) @ 
% 0.34/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.34/0.52      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.34/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.52        | (v2_struct_0 @ sk_B)
% 0.34/0.52        | ~ (v2_pre_topc @ sk_B)
% 0.34/0.52        | ~ (l1_pre_topc @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.52  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.34/0.52  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.34/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.52        | (v2_struct_0 @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.34/0.52  thf('23', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      ((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.34/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.34/0.52  thf(t5_subset, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.34/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.34/0.52          | ~ (v1_xboole_0 @ X7)
% 0.34/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.52          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.34/0.52  thf('27', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('28', plain, (((sk_D) = (sk_E))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('29', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      (![X19 : $i, X20 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.34/0.52          | (r2_hidden @ X19 @ (k1_connsp_2 @ X20 @ X19))
% 0.34/0.52          | ~ (l1_pre_topc @ X20)
% 0.34/0.52          | ~ (v2_pre_topc @ X20)
% 0.34/0.52          | (v2_struct_0 @ X20))),
% 0.34/0.52      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (((v2_struct_0 @ sk_A)
% 0.34/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.52        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.52  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.34/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.34/0.52  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('36', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_A @ sk_D))),
% 0.34/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.34/0.52  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.34/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      (![X15 : $i, X16 : $i]:
% 0.34/0.52         ((v1_xboole_0 @ X15)
% 0.34/0.52          | ~ (m1_subset_1 @ X16 @ X15)
% 0.34/0.52          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.34/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.34/0.52  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('41', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t2_subset, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.34/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      (![X3 : $i, X4 : $i]:
% 0.34/0.52         ((r2_hidden @ X3 @ X4)
% 0.34/0.52          | (v1_xboole_0 @ X4)
% 0.34/0.52          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.34/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.52        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.34/0.52  thf(t63_subset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.34/0.52       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      (![X1 : $i, X2 : $i]:
% 0.34/0.52         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.34/0.52          | ~ (r2_hidden @ X1 @ X2))),
% 0.34/0.52      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.34/0.52  thf('45', plain,
% 0.34/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.52        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.34/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.52  thf(t39_pre_topc, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.34/0.52               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.34/0.52         (~ (m1_pre_topc @ X12 @ X13)
% 0.34/0.52          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.34/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.34/0.52          | ~ (l1_pre_topc @ X13))),
% 0.34/0.52      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.34/0.52  thf('47', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.52          | ~ (l1_pre_topc @ X0)
% 0.34/0.52          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.34/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.34/0.52          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.34/0.52  thf('48', plain,
% 0.34/0.52      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.34/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['40', '47'])).
% 0.34/0.52  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('50', plain,
% 0.34/0.52      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.34/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.34/0.52  thf('51', plain,
% 0.34/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.52        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.34/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.52  thf('52', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_C @ 
% 0.34/0.52        (k1_zfmisc_1 @ 
% 0.34/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t76_tex_2, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.34/0.52         ( l1_pre_topc @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.34/0.52             ( m1_pre_topc @ B @ A ) ) =>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.34/0.52                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.34/0.52                 ( m1_subset_1 @
% 0.34/0.52                   C @ 
% 0.34/0.52                   ( k1_zfmisc_1 @
% 0.34/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.34/0.52               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.34/0.52                 ( ![D:$i]:
% 0.34/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.34/0.52                     ( ![E:$i]:
% 0.34/0.52                       ( ( m1_subset_1 @
% 0.34/0.52                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52                         ( ( ( D ) = ( E ) ) =>
% 0.34/0.52                           ( ( k8_relset_1 @
% 0.34/0.52                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.34/0.52                               D ) =
% 0.34/0.52                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf('53', plain,
% 0.34/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.34/0.52         ((v2_struct_0 @ X21)
% 0.34/0.52          | ~ (v4_tex_2 @ X21 @ X22)
% 0.34/0.52          | ~ (m1_pre_topc @ X21 @ X22)
% 0.34/0.52          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.34/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.34/0.52          | ((X24) != (X25))
% 0.34/0.52          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.34/0.52              X24) = (k2_pre_topc @ X22 @ X25))
% 0.34/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.34/0.52          | ~ (m1_subset_1 @ X23 @ 
% 0.34/0.52               (k1_zfmisc_1 @ 
% 0.34/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.34/0.52          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.34/0.52          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.34/0.52          | ~ (v1_funct_1 @ X23)
% 0.34/0.52          | ~ (l1_pre_topc @ X22)
% 0.34/0.52          | ~ (v3_tdlat_3 @ X22)
% 0.34/0.52          | ~ (v2_pre_topc @ X22)
% 0.34/0.52          | (v2_struct_0 @ X22))),
% 0.34/0.52      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.34/0.52  thf('54', plain,
% 0.34/0.52      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.34/0.52         ((v2_struct_0 @ X22)
% 0.34/0.52          | ~ (v2_pre_topc @ X22)
% 0.34/0.52          | ~ (v3_tdlat_3 @ X22)
% 0.34/0.52          | ~ (l1_pre_topc @ X22)
% 0.34/0.52          | ~ (v1_funct_1 @ X23)
% 0.34/0.52          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.34/0.52          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.34/0.52          | ~ (m1_subset_1 @ X23 @ 
% 0.34/0.52               (k1_zfmisc_1 @ 
% 0.34/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.34/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.34/0.52          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.34/0.52              X25) = (k2_pre_topc @ X22 @ X25))
% 0.34/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.34/0.52          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.34/0.52          | ~ (m1_pre_topc @ X21 @ X22)
% 0.34/0.52          | ~ (v4_tex_2 @ X21 @ X22)
% 0.34/0.52          | (v2_struct_0 @ X21))),
% 0.34/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.34/0.52  thf('55', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((v2_struct_0 @ sk_B)
% 0.34/0.52          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.34/0.52          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.34/0.52          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.34/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.52          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.52              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.34/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.52          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.34/0.52          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.34/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.34/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.34/0.52          | ~ (v3_tdlat_3 @ sk_A)
% 0.34/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.34/0.52          | (v2_struct_0 @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['52', '54'])).
% 0.34/0.52  thf('56', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('58', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('59', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('60', plain,
% 0.34/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('63', plain, ((v3_tdlat_3 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('65', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((v2_struct_0 @ sk_B)
% 0.34/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.52          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.52              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.34/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.52          | (v2_struct_0 @ sk_A))),
% 0.34/0.52      inference('demod', [status(thm)],
% 0.34/0.52                ['55', '56', '57', '58', '59', '60', '61', '62', '63', '64'])).
% 0.34/0.52  thf('66', plain,
% 0.34/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.52        | (v2_struct_0 @ sk_A)
% 0.34/0.52        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.34/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.52            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.34/0.52        | (v2_struct_0 @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['51', '65'])).
% 0.34/0.52  thf('67', plain,
% 0.34/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.52        | (v2_struct_0 @ sk_B)
% 0.34/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.53            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['50', '66'])).
% 0.34/0.53  thf('68', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.53            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.34/0.53        | (v2_struct_0 @ sk_B)
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['67'])).
% 0.34/0.53  thf('69', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('70', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i]:
% 0.34/0.53         ((v1_xboole_0 @ X15)
% 0.34/0.53          | ~ (m1_subset_1 @ X16 @ X15)
% 0.34/0.53          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.34/0.53  thf('71', plain,
% 0.34/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.34/0.53  thf('72', plain,
% 0.34/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.34/0.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('73', plain, (((sk_D) = (sk_E))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('74', plain,
% 0.34/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.34/0.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.34/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.34/0.53  thf('75', plain,
% 0.34/0.53      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.53          (k1_tarski @ sk_D))
% 0.34/0.53          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['71', '74'])).
% 0.34/0.53  thf('76', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.34/0.53          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.53        | (v2_struct_0 @ sk_B)
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['68', '75'])).
% 0.34/0.53  thf('77', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_B)
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.53        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.34/0.53            != (k2_pre_topc @ sk_A @ 
% 0.34/0.53                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.34/0.53      inference('simplify', [status(thm)], ['76'])).
% 0.34/0.53  thf('78', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.34/0.53          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.53        | (v2_struct_0 @ sk_B)
% 0.34/0.53        | (v2_struct_0 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['39', '77'])).
% 0.34/0.53  thf('79', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_B)
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['78'])).
% 0.34/0.53  thf('80', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('81', plain,
% 0.34/0.53      (![X17 : $i, X18 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X17)
% 0.34/0.53          | ~ (v2_pre_topc @ X17)
% 0.34/0.53          | (v2_struct_0 @ X17)
% 0.34/0.53          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.34/0.53          | (m1_subset_1 @ (k1_connsp_2 @ X17 @ X18) @ 
% 0.34/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.34/0.53  thf('82', plain,
% 0.34/0.53      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_D) @ 
% 0.34/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.34/0.53  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('85', plain,
% 0.34/0.53      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_D) @ 
% 0.34/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.53        | (v2_struct_0 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.34/0.53  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('87', plain,
% 0.34/0.53      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_D) @ 
% 0.34/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('clc', [status(thm)], ['85', '86'])).
% 0.34/0.53  thf('88', plain,
% 0.34/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X5 @ X6)
% 0.34/0.53          | ~ (v1_xboole_0 @ X7)
% 0.34/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.34/0.53  thf('89', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.34/0.53          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['87', '88'])).
% 0.34/0.53  thf('90', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.34/0.53          | (v2_struct_0 @ sk_B)
% 0.34/0.53          | (v2_struct_0 @ sk_A)
% 0.34/0.53          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['79', '89'])).
% 0.34/0.53  thf('91', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_B)
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['36', '90'])).
% 0.34/0.53  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('93', plain,
% 0.34/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.34/0.53      inference('clc', [status(thm)], ['91', '92'])).
% 0.34/0.53  thf('94', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('95', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.34/0.53      inference('clc', [status(thm)], ['93', '94'])).
% 0.34/0.53  thf('96', plain,
% 0.34/0.53      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_D))),
% 0.34/0.53      inference('demod', [status(thm)], ['26', '95'])).
% 0.34/0.53  thf('97', plain, ($false), inference('sup-', [status(thm)], ['16', '96'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
