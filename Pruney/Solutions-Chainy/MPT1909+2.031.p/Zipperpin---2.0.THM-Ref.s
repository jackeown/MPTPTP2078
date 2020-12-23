%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GG28gtH9J8

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 385 expanded)
%              Number of leaves         :   37 ( 127 expanded)
%              Depth                    :   25
%              Number of atoms          : 1226 (11107 expanded)
%              Number of equality atoms :   37 ( 314 expanded)
%              Maximal formula depth    :   23 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ X4 )
      | ( ( k6_domain_1 @ X4 @ X5 )
        = ( k1_tarski @ X5 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ X4 )
      | ( ( k6_domain_1 @ X4 @ X5 )
        = ( k1_tarski @ X5 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) @ X14 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('29',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k1_tex_2 @ X12 @ X11 ) )
      | ( ( u1_struct_0 @ X13 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( v1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) @ X12 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['20','21'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('43',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['40','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','50'])).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v4_tex_2 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v3_borsuk_1 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( X19 != X20 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 @ X19 )
        = ( k2_pre_topc @ X17 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v5_pre_topc @ X18 @ X17 @ X16 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v5_pre_topc @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 @ X20 )
        = ( k2_pre_topc @ X17 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_borsuk_1 @ X18 @ X17 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v4_tex_2 @ X16 @ X17 )
      | ( v2_struct_0 @ X16 ) ) ),
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
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['20','21'])).

thf('68',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ B )
             => ( m1_pre_topc @ C @ A ) ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_pre_topc @ X10 @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('80',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','80'])).

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
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
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
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GG28gtH9J8
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:28:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 96 iterations in 0.035s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.51  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.51  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(t77_tex_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                     ( ![E:$i]:
% 0.20/0.51                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.51                           ( ( k8_relset_1 @
% 0.20/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.51                             ( k2_pre_topc @
% 0.20/0.51                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.51                ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                    ( v1_funct_2 @
% 0.20/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.51                    ( m1_subset_1 @
% 0.20/0.51                      C @ 
% 0.20/0.51                      ( k1_zfmisc_1 @
% 0.20/0.51                        ( k2_zfmisc_1 @
% 0.20/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.51                    ( ![D:$i]:
% 0.20/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                        ( ![E:$i]:
% 0.20/0.51                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                            ( ( ( D ) = ( E ) ) =>
% 0.20/0.51                              ( ( k8_relset_1 @
% 0.20/0.51                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.51                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.51                                ( k2_pre_topc @
% 0.20/0.51                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ X4)
% 0.20/0.51          | ((k6_domain_1 @ X4 @ X5) = (k1_tarski @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, (((sk_D) = (sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ X4)
% 0.20/0.51          | ((k6_domain_1 @ X4 @ X5) = (k1_tarski @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, (((sk_D) = (sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k1_tex_2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.51         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.51         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.20/0.51          | (m1_pre_topc @ (k1_tex_2 @ X14 @ X15) @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.51  thf('21', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf(t1_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( m1_subset_1 @
% 0.20/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X6) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51          | ~ (l1_pre_topc @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.20/0.51          | (v1_pre_topc @ (k1_tex_2 @ X14 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf(d4_tex_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.51                 ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.20/0.51                 ( ( u1_struct_0 @ C ) =
% 0.20/0.51                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.51          | ((X13) != (k1_tex_2 @ X12 @ X11))
% 0.20/0.51          | ((u1_struct_0 @ X13) = (k6_domain_1 @ (u1_struct_0 @ X12) @ X11))
% 0.20/0.51          | ~ (m1_pre_topc @ X13 @ X12)
% 0.20/0.51          | ~ (v1_pre_topc @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13)
% 0.20/0.51          | ~ (l1_pre_topc @ X12)
% 0.20/0.51          | (v2_struct_0 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X12)
% 0.20/0.51          | ~ (l1_pre_topc @ X12)
% 0.20/0.51          | (v2_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.20/0.51          | ~ (v1_pre_topc @ (k1_tex_2 @ X12 @ X11))
% 0.20/0.51          | ~ (m1_pre_topc @ (k1_tex_2 @ X12 @ X11) @ X12)
% 0.20/0.51          | ((u1_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.20/0.51              = (k6_domain_1 @ (u1_struct_0 @ X12) @ X11))
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.51  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51          = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.20/0.51  thf('41', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.20/0.51          | ~ (v2_struct_0 @ (k1_tex_2 @ X14 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))),
% 0.20/0.51      inference('clc', [status(thm)], ['40', '47'])).
% 0.20/0.51  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51         = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t76_tex_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51                     ( ![E:$i]:
% 0.20/0.51                       ( ( m1_subset_1 @
% 0.20/0.51                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.51                           ( ( k8_relset_1 @
% 0.20/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                               D ) =
% 0.20/0.51                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X16)
% 0.20/0.51          | ~ (v4_tex_2 @ X16 @ X17)
% 0.20/0.51          | ~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.51          | ~ (v3_borsuk_1 @ X18 @ X17 @ X16)
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.51          | ((X19) != (X20))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18 @ 
% 0.20/0.51              X19) = (k2_pre_topc @ X17 @ X20))
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.20/0.51          | ~ (v5_pre_topc @ X18 @ X17 @ X16)
% 0.20/0.51          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.51          | ~ (v1_funct_1 @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X17)
% 0.20/0.51          | ~ (v3_tdlat_3 @ X17)
% 0.20/0.51          | ~ (v2_pre_topc @ X17)
% 0.20/0.51          | (v2_struct_0 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X17)
% 0.20/0.51          | ~ (v2_pre_topc @ X17)
% 0.20/0.51          | ~ (v3_tdlat_3 @ X17)
% 0.20/0.51          | ~ (l1_pre_topc @ X17)
% 0.20/0.51          | ~ (v1_funct_1 @ X18)
% 0.20/0.51          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.51          | ~ (v5_pre_topc @ X18 @ X17 @ X16)
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18 @ 
% 0.20/0.51              X20) = (k2_pre_topc @ X17 @ X20))
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.51          | ~ (v3_borsuk_1 @ X18 @ X17 @ X16)
% 0.20/0.51          | ~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.51          | ~ (v4_tex_2 @ X16 @ X17)
% 0.20/0.51          | (v2_struct_0 @ X16))),
% 0.20/0.51      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.51          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '54'])).
% 0.20/0.51  thf('56', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('63', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['55', '56', '57', '58', '59', '60', '61', '62', '63', '64'])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['51', '65'])).
% 0.20/0.51  thf('67', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('68', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t7_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.51          | (m1_pre_topc @ X10 @ X9)
% 0.20/0.51          | ~ (m1_pre_topc @ X10 @ X8)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_B) | (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.51  thf('74', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['67', '73'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X6) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51          | ~ (l1_pre_topc @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.51  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.51         = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['66', '80'])).
% 0.20/0.51  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.20/0.51      inference('clc', [status(thm)], ['81', '82'])).
% 0.20/0.51  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51         = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))),
% 0.20/0.51      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '85'])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      ((((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.51          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '87'])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['88'])).
% 0.20/0.51  thf(fc2_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      (![X3 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.20/0.51          | ~ (l1_struct_0 @ X3)
% 0.20/0.51          | (v2_struct_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.51  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_l1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('93', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['91', '94'])).
% 0.20/0.51  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (![X3 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.20/0.51          | ~ (l1_struct_0 @ X3)
% 0.20/0.51          | (v2_struct_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.51  thf('99', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.51  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('101', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.51  thf('103', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['99', '102'])).
% 0.20/0.51  thf('104', plain, ($false), inference('demod', [status(thm)], ['0', '103'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
