%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WejIbcADz3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 468 expanded)
%              Number of leaves         :   40 ( 151 expanded)
%              Depth                    :   29
%              Number of atoms          : 1343 (13700 expanded)
%              Number of equality atoms :   37 ( 378 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X22 @ X23 ) @ X22 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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

thf('23',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['20','21'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_pre_topc @ X18 @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['23','29'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( r1_tarski @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('43',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( X21
       != ( k1_tex_2 @ X20 @ X19 ) )
      | ( ( u1_struct_0 @ X21 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( v1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X20 @ X19 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X20 @ X19 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X20 @ X19 ) @ X20 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X20 @ X19 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['20','21'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('54',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('57',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('59',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['54','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','64'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v4_tex_2 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v3_borsuk_1 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( X27 != X28 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) @ X26 @ X27 )
        = ( k2_pre_topc @ X25 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v5_pre_topc @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v3_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('68',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( v3_tdlat_3 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) @ X26 @ X28 )
        = ( k2_pre_topc @ X25 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_borsuk_1 @ X26 @ X25 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v4_tex_2 @ X24 @ X25 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
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
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('89',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','94'])).

thf('96',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','95'])).

thf('97',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('99',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('102',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('110',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['0','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WejIbcADz3
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 134 iterations in 0.074s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.53  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.53  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(t77_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.53             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.53                 ( m1_subset_1 @
% 0.20/0.53                   C @ 
% 0.20/0.53                   ( k1_zfmisc_1 @
% 0.20/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.53                 ( ![D:$i]:
% 0.20/0.53                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                     ( ![E:$i]:
% 0.20/0.53                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.53                           ( ( k8_relset_1 @
% 0.20/0.53                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.53                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.53                             ( k2_pre_topc @
% 0.20/0.53                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.53                ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                    ( v1_funct_2 @
% 0.20/0.53                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.53                    ( m1_subset_1 @
% 0.20/0.53                      C @ 
% 0.20/0.53                      ( k1_zfmisc_1 @
% 0.20/0.53                        ( k2_zfmisc_1 @
% 0.20/0.53                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.53                    ( ![D:$i]:
% 0.20/0.53                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                        ( ![E:$i]:
% 0.20/0.53                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                            ( ( ( D ) = ( E ) ) =>
% 0.20/0.53                              ( ( k8_relset_1 @
% 0.20/0.53                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.53                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.53                                ( k2_pre_topc @
% 0.20/0.53                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.20/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X11)
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ X11)
% 0.20/0.53          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('5', plain, (((sk_D) = (sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X11)
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ X11)
% 0.20/0.53          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain, (((sk_D) = (sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k1_tex_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.53         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.53         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X22)
% 0.20/0.53          | (v2_struct_0 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.53          | (m1_pre_topc @ (k1_tex_2 @ X22 @ X23) @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_B)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_m1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.53  thf('21', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('22', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.20/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.20/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t7_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.53          | (m1_pre_topc @ X18 @ X17)
% 0.20/0.53          | ~ (m1_pre_topc @ X18 @ X16)
% 0.20/0.53          | ~ (l1_pre_topc @ X17)
% 0.20/0.53          | ~ (v2_pre_topc @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.53          | (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_B) | (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.53  thf('30', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '29'])).
% 0.20/0.53  thf(t4_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.53               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.53                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.53          | ~ (m1_pre_topc @ X13 @ X15)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.20/0.53          | ~ (m1_pre_topc @ X15 @ X14)
% 0.20/0.53          | ~ (l1_pre_topc @ X14)
% 0.20/0.53          | ~ (v2_pre_topc @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53             (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53             (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53         (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '35'])).
% 0.20/0.53  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53        (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X22)
% 0.20/0.53          | (v2_struct_0 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.53          | (v1_pre_topc @ (k1_tex_2 @ X22 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53        | (v2_struct_0 @ sk_B)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.20/0.53      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf(d4_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.53                 ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.53               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.20/0.53                 ( ( u1_struct_0 @ C ) =
% 0.20/0.53                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.20/0.53          | ((X21) != (k1_tex_2 @ X20 @ X19))
% 0.20/0.53          | ((u1_struct_0 @ X21) = (k6_domain_1 @ (u1_struct_0 @ X20) @ X19))
% 0.20/0.53          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.53          | ~ (v1_pre_topc @ X21)
% 0.20/0.53          | (v2_struct_0 @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X20)
% 0.20/0.53          | (v2_struct_0 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X20)
% 0.20/0.53          | ~ (l1_pre_topc @ X20)
% 0.20/0.53          | (v2_struct_0 @ (k1_tex_2 @ X20 @ X19))
% 0.20/0.53          | ~ (v1_pre_topc @ (k1_tex_2 @ X20 @ X19))
% 0.20/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ X20 @ X19) @ X20)
% 0.20/0.53          | ((u1_struct_0 @ (k1_tex_2 @ X20 @ X19))
% 0.20/0.53              = (k6_domain_1 @ (u1_struct_0 @ X20) @ X19))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '49'])).
% 0.20/0.53  thf('51', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('52', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.20/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53          = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.20/0.53  thf('55', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X22)
% 0.20/0.53          | (v2_struct_0 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.53          | ~ (v2_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53        | (v2_struct_0 @ sk_B)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('61', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.20/0.53      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['54', '61'])).
% 0.20/0.53  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53         = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.20/0.53      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t76_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.53             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.53                 ( m1_subset_1 @
% 0.20/0.53                   C @ 
% 0.20/0.53                   ( k1_zfmisc_1 @
% 0.20/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.53                 ( ![D:$i]:
% 0.20/0.53                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53                     ( ![E:$i]:
% 0.20/0.53                       ( ( m1_subset_1 @
% 0.20/0.53                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.53                           ( ( k8_relset_1 @
% 0.20/0.53                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.53                               D ) =
% 0.20/0.53                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X24)
% 0.20/0.53          | ~ (v4_tex_2 @ X24 @ X25)
% 0.20/0.53          | ~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.53          | ~ (v3_borsuk_1 @ X26 @ X25 @ X24)
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.53          | ((X27) != (X28))
% 0.20/0.53          | ((k8_relset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24) @ X26 @ 
% 0.20/0.53              X27) = (k2_pre_topc @ X25 @ X28))
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.20/0.53          | ~ (v5_pre_topc @ X26 @ X25 @ X24)
% 0.20/0.53          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (v1_funct_1 @ X26)
% 0.20/0.53          | ~ (l1_pre_topc @ X25)
% 0.20/0.53          | ~ (v3_tdlat_3 @ X25)
% 0.20/0.53          | ~ (v2_pre_topc @ X25)
% 0.20/0.53          | (v2_struct_0 @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X25)
% 0.20/0.53          | ~ (v2_pre_topc @ X25)
% 0.20/0.53          | ~ (v3_tdlat_3 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X25)
% 0.20/0.53          | ~ (v1_funct_1 @ X26)
% 0.20/0.53          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (v5_pre_topc @ X26 @ X25 @ X24)
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.53          | ((k8_relset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24) @ X26 @ 
% 0.20/0.53              X28) = (k2_pre_topc @ X25 @ X28))
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.53          | ~ (v3_borsuk_1 @ X26 @ X25 @ X24)
% 0.20/0.53          | ~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.53          | ~ (v4_tex_2 @ X24 @ X25)
% 0.20/0.53          | (v2_struct_0 @ X24))),
% 0.20/0.53      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.53          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['66', '68'])).
% 0.20/0.53  thf('70', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('72', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('73', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('77', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['69', '70', '71', '72', '73', '74', '75', '76', '77', '78'])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['65', '79'])).
% 0.20/0.53  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf(t39_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.53          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.53          | ~ (l1_pre_topc @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['81', '84'])).
% 0.20/0.53  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.20/0.53         = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.20/0.53      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '89'])).
% 0.20/0.53  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.20/0.53      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.53  thf('93', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53         = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '94'])).
% 0.20/0.53  thf('96', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.53          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '95'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.53          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '96'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['97'])).
% 0.20/0.53  thf(fc2_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (![X7 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.20/0.53          | ~ (l1_struct_0 @ X7)
% 0.20/0.53          | (v2_struct_0 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.53  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_l1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.53  thf('102', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['100', '103'])).
% 0.20/0.53  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('106', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['104', '105'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (![X7 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.20/0.53          | ~ (l1_struct_0 @ X7)
% 0.20/0.53          | (v2_struct_0 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('108', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.53  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('110', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.53  thf('112', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['108', '111'])).
% 0.20/0.53  thf('113', plain, ($false), inference('demod', [status(thm)], ['0', '112'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
