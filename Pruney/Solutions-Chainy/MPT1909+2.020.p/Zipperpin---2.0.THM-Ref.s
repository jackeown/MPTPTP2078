%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zPxoIwvW8l

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 404 expanded)
%              Number of leaves         :   39 ( 133 expanded)
%              Depth                    :   25
%              Number of atoms          : 1250 (11252 expanded)
%              Number of equality atoms :   39 ( 318 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
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

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('14',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('34',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('36',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( X18
       != ( k1_tex_2 @ X17 @ X16 ) )
      | ( ( u1_struct_0 @ X18 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( v1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X17 @ X16 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X17 @ X16 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X17 @ X16 ) @ X17 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X17 @ X16 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['20','21'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('48',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('50',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['45','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','55'])).

thf('57',plain,(
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

thf('58',plain,(
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

thf('59',plain,(
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
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65','66','67','68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('80',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','85'])).

thf('87',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','86'])).

thf('88',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('90',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('93',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('101',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['99','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zPxoIwvW8l
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 156 iterations in 0.071s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.52  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.21/0.52  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(t77_tex_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.52             ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.52                 ( m1_subset_1 @
% 0.21/0.52                   C @ 
% 0.21/0.52                   ( k1_zfmisc_1 @
% 0.21/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                     ( ![E:$i]:
% 0.21/0.52                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                         ( ( ( D ) = ( E ) ) =>
% 0.21/0.52                           ( ( k8_relset_1 @
% 0.21/0.52                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.52                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.21/0.52                             ( k2_pre_topc @
% 0.21/0.52                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.52                ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                    ( v1_funct_2 @
% 0.21/0.52                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.52                    ( m1_subset_1 @
% 0.21/0.52                      C @ 
% 0.21/0.52                      ( k1_zfmisc_1 @
% 0.21/0.52                        ( k2_zfmisc_1 @
% 0.21/0.52                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.52                    ( ![D:$i]:
% 0.21/0.52                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                        ( ![E:$i]:
% 0.21/0.52                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                            ( ( ( D ) = ( E ) ) =>
% 0.21/0.52                              ( ( k8_relset_1 @
% 0.21/0.52                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.52                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.21/0.52                                ( k2_pre_topc @
% 0.21/0.52                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ X14)
% 0.21/0.52          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain, (((sk_D) = (sk_E))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ X14)
% 0.21/0.52          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.52         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, (((sk_D) = (sk_E))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.52         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k1_tex_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.52         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X19)
% 0.21/0.52          | (v2_struct_0 @ X19)
% 0.21/0.52          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.52          | (m1_pre_topc @ (k1_tex_2 @ X19 @ X20) @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_B)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '19'])).
% 0.21/0.53  thf('21', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X4 : $i, X6 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf(t39_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.53          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.53          | ~ (l1_pre_topc @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X1)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '28'])).
% 0.21/0.53  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X19)
% 0.21/0.53          | (v2_struct_0 @ X19)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.53          | (v1_pre_topc @ (k1_tex_2 @ X19 @ X20)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53        | (v2_struct_0 @ sk_B)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.21/0.53      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf(d4_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.21/0.53                 ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.21/0.53                 ( ( u1_struct_0 @ C ) =
% 0.21/0.53                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.53          | ((X18) != (k1_tex_2 @ X17 @ X16))
% 0.21/0.53          | ((u1_struct_0 @ X18) = (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 0.21/0.53          | ~ (m1_pre_topc @ X18 @ X17)
% 0.21/0.53          | ~ (v1_pre_topc @ X18)
% 0.21/0.53          | (v2_struct_0 @ X18)
% 0.21/0.53          | ~ (l1_pre_topc @ X17)
% 0.21/0.53          | (v2_struct_0 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X17)
% 0.21/0.53          | ~ (l1_pre_topc @ X17)
% 0.21/0.53          | (v2_struct_0 @ (k1_tex_2 @ X17 @ X16))
% 0.21/0.53          | ~ (v1_pre_topc @ (k1_tex_2 @ X17 @ X16))
% 0.21/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ X17 @ X16) @ X17)
% 0.21/0.53          | ((u1_struct_0 @ (k1_tex_2 @ X17 @ X16))
% 0.21/0.53              = (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 0.21/0.53          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.21/0.53        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '40'])).
% 0.21/0.53  thf('42', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53          = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.21/0.53  thf('46', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X19)
% 0.21/0.53          | (v2_struct_0 @ X19)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.53          | ~ (v2_struct_0 @ (k1_tex_2 @ X19 @ X20)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53        | (v2_struct_0 @ sk_B)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.21/0.53      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))),
% 0.21/0.53      inference('clc', [status(thm)], ['45', '52'])).
% 0.21/0.53  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53         = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.21/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '55'])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t76_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.53         ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.53             ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.53                 ( ![D:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                     ( ![E:$i]:
% 0.21/0.53                       ( ( m1_subset_1 @
% 0.21/0.53                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                         ( ( ( D ) = ( E ) ) =>
% 0.21/0.53                           ( ( k8_relset_1 @
% 0.21/0.53                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.53                               D ) =
% 0.21/0.53                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X21)
% 0.21/0.53          | ~ (v4_tex_2 @ X21 @ X22)
% 0.21/0.53          | ~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.53          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.21/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | ((X24) != (X25))
% 0.21/0.53          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.21/0.53              X24) = (k2_pre_topc @ X22 @ X25))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.53          | ~ (m1_subset_1 @ X23 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.21/0.53          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.21/0.53          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.21/0.53          | ~ (v1_funct_1 @ X23)
% 0.21/0.53          | ~ (l1_pre_topc @ X22)
% 0.21/0.53          | ~ (v3_tdlat_3 @ X22)
% 0.21/0.53          | ~ (v2_pre_topc @ X22)
% 0.21/0.53          | (v2_struct_0 @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X22)
% 0.21/0.53          | ~ (v2_pre_topc @ X22)
% 0.21/0.53          | ~ (v3_tdlat_3 @ X22)
% 0.21/0.53          | ~ (l1_pre_topc @ X22)
% 0.21/0.53          | ~ (v1_funct_1 @ X23)
% 0.21/0.53          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.21/0.53          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.21/0.53          | ~ (m1_subset_1 @ X23 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.53          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.21/0.53              X25) = (k2_pre_topc @ X22 @ X25))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.21/0.53          | ~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.53          | ~ (v4_tex_2 @ X21 @ X22)
% 0.21/0.53          | (v2_struct_0 @ X21))),
% 0.21/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.53          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.53              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['57', '59'])).
% 0.21/0.53  thf('61', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('63', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('64', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('68', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.53              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['60', '61', '62', '63', '64', '65', '66', '67', '68', '69'])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '70'])).
% 0.21/0.53  thf('72', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.53          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.53          | ~ (l1_pre_topc @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['72', '75'])).
% 0.21/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      (((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.53         = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.21/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['71', '80'])).
% 0.21/0.53  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.21/0.53      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.53  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53         = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))),
% 0.21/0.53      inference('clc', [status(thm)], ['83', '84'])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '85'])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      ((((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.53          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '86'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.21/0.53          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '87'])).
% 0.21/0.53  thf('89', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.53  thf(fc2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (![X10 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ~ (l1_struct_0 @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.53  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('93', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['91', '94'])).
% 0.21/0.53  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('97', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      (![X10 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ~ (l1_struct_0 @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('99', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.53  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('101', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.53  thf('103', plain, ((v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['99', '102'])).
% 0.21/0.53  thf('104', plain, ($false), inference('demod', [status(thm)], ['0', '103'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
