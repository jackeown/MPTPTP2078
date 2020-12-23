%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jXzOcE3cJj

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 259 expanded)
%              Number of leaves         :   36 (  91 expanded)
%              Depth                    :   20
%              Number of atoms          : 1219 (7706 expanded)
%              Number of equality atoms :   28 ( 220 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X17 @ ( k1_connsp_2 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X17 @ ( k1_connsp_2 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
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

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('43',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('55',plain,(
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

thf('56',plain,(
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

thf('57',plain,(
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
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
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
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64','65','66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('73',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('82',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','96'])).

thf('98',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jXzOcE3cJj
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 131 iterations in 0.061s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(t77_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                     ( ![E:$i]:
% 0.21/0.51                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.21/0.51                           ( ( k8_relset_1 @
% 0.21/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.51                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.21/0.51                             ( k2_pre_topc @
% 0.21/0.51                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.51                ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                    ( v1_funct_2 @
% 0.21/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.51                    ( m1_subset_1 @
% 0.21/0.51                      C @ 
% 0.21/0.51                      ( k1_zfmisc_1 @
% 0.21/0.51                        ( k2_zfmisc_1 @
% 0.21/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.51                    ( ![D:$i]:
% 0.21/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                        ( ![E:$i]:
% 0.21/0.51                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                            ( ( ( D ) = ( E ) ) =>
% 0.21/0.51                              ( ( k8_relset_1 @
% 0.21/0.51                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.51                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.21/0.51                                ( k2_pre_topc @
% 0.21/0.51                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.21/0.51  thf('0', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t30_connsp_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.21/0.51          | (r2_hidden @ X17 @ (k1_connsp_2 @ X18 @ X17))
% 0.21/0.51          | ~ (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (v2_pre_topc @ X18)
% 0.21/0.51          | (v2_struct_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.51          | (v2_pre_topc @ X4)
% 0.21/0.51          | ~ (l1_pre_topc @ X5)
% 0.21/0.51          | ~ (v2_pre_topc @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.51  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B) | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '8', '13'])).
% 0.21/0.51  thf('15', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k1_connsp_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X15)
% 0.21/0.51          | ~ (v2_pre_topc @ X15)
% 0.21/0.51          | (v2_struct_0 @ X15)
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.21/0.51          | (m1_subset_1 @ (k1_connsp_2 @ X15 @ X16) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.51  thf('23', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf(t5_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X1 @ X2)
% 0.21/0.51          | ~ (v1_xboole_0 @ X3)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, (((sk_D) = (sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.21/0.51          | (r2_hidden @ X17 @ (k1_connsp_2 @ X18 @ X17))
% 0.21/0.51          | ~ (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (v2_pre_topc @ X18)
% 0.21/0.51          | (v2_struct_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.51  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_A @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ X13)
% 0.21/0.51          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ X13)
% 0.21/0.51          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k6_domain_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X11)
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ X11)
% 0.21/0.51          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['43', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.51  thf(t39_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.51          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '50'])).
% 0.21/0.51  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t76_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                     ( ![E:$i]:
% 0.21/0.51                       ( ( m1_subset_1 @
% 0.21/0.51                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.21/0.51                           ( ( k8_relset_1 @
% 0.21/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.51                               D ) =
% 0.21/0.51                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X19)
% 0.21/0.51          | ~ (v4_tex_2 @ X19 @ X20)
% 0.21/0.51          | ~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.51          | ~ (v3_borsuk_1 @ X21 @ X20 @ X19)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.51          | ((X22) != (X23))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21 @ 
% 0.21/0.51              X22) = (k2_pre_topc @ X20 @ X23))
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.21/0.51          | ~ (v5_pre_topc @ X21 @ X20 @ X19)
% 0.21/0.51          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.21/0.51          | ~ (v1_funct_1 @ X21)
% 0.21/0.51          | ~ (l1_pre_topc @ X20)
% 0.21/0.51          | ~ (v3_tdlat_3 @ X20)
% 0.21/0.51          | ~ (v2_pre_topc @ X20)
% 0.21/0.51          | (v2_struct_0 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X20)
% 0.21/0.51          | ~ (v2_pre_topc @ X20)
% 0.21/0.51          | ~ (v3_tdlat_3 @ X20)
% 0.21/0.51          | ~ (l1_pre_topc @ X20)
% 0.21/0.51          | ~ (v1_funct_1 @ X21)
% 0.21/0.51          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.21/0.51          | ~ (v5_pre_topc @ X21 @ X20 @ X19)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21 @ 
% 0.21/0.51              X23) = (k2_pre_topc @ X20 @ X23))
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.51          | ~ (v3_borsuk_1 @ X21 @ X20 @ X19)
% 0.21/0.51          | ~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.51          | ~ (v4_tex_2 @ X19 @ X20)
% 0.21/0.51          | (v2_struct_0 @ X19))),
% 0.21/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.51          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['55', '57'])).
% 0.21/0.51  thf('59', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('62', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['58', '59', '60', '61', '62', '63', '64', '65', '66', '67'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '68'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('74', plain, (((sk_D) = (sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51          (k1_tarski @ sk_D))
% 0.21/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.21/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '76'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.21/0.51            != (k2_pre_topc @ sk_A @ 
% 0.21/0.51                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.21/0.51          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '78'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['79'])).
% 0.21/0.51  thf('81', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X15)
% 0.21/0.51          | ~ (v2_pre_topc @ X15)
% 0.21/0.51          | (v2_struct_0 @ X15)
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.21/0.51          | (m1_subset_1 @ (k1_connsp_2 @ X15 @ X16) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.21/0.51  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X1 @ X2)
% 0.21/0.51          | ~ (v1_xboole_0 @ X3)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['80', '90'])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '91'])).
% 0.21/0.51  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['92', '93'])).
% 0.21/0.51  thf('95', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '96'])).
% 0.21/0.51  thf('98', plain, ($false), inference('sup-', [status(thm)], ['16', '97'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
