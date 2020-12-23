%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tGPVOnnJwP

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 372 expanded)
%              Number of leaves         :   36 ( 122 expanded)
%              Depth                    :   26
%              Number of atoms          : 1446 (10962 expanded)
%              Number of equality atoms :   42 ( 321 expanded)
%              Maximal formula depth    :   23 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( ( k6_domain_1 @ X5 @ X6 )
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('20',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) ),
    inference(clc,[status(thm)],['22','23'])).

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

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k1_tex_2 @ X10 @ X9 ) )
      | ( ( u1_struct_0 @ X11 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X10 ) @ X9 ) )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X10 @ X9 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X10 @ X9 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X10 @ X9 ) @ X10 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X10 @ X9 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X10 ) @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('29',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('34',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['31','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( ( k6_domain_1 @ X5 @ X6 )
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('46',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('49',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('61',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('64',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('66',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X10 @ X9 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X10 @ X9 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X10 @ X9 ) @ X10 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X10 @ X9 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X10 ) @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('70',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['55','56'])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('77',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('79',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['74','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B @ sk_D ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','85'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v4_tex_2 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( v3_borsuk_1 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X17 != X18 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) @ X16 @ X17 )
        = ( k2_pre_topc @ X15 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v5_pre_topc @ X16 @ X15 @ X14 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v3_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('89',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( v3_tdlat_3 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v5_pre_topc @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) @ X16 @ X18 )
        = ( k2_pre_topc @ X15 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_borsuk_1 @ X16 @ X15 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( v4_tex_2 @ X14 @ X15 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
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
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96','97','98','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','101'])).

thf('103',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('104',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('112',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('115',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('126',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['124','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tGPVOnnJwP
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:15:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 95 iterations in 0.048s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.21/0.50  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(t77_tex_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.50         ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.50             ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.50                 ( m1_subset_1 @
% 0.21/0.50                   C @ 
% 0.21/0.50                   ( k1_zfmisc_1 @
% 0.21/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.50                 ( ![D:$i]:
% 0.21/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                     ( ![E:$i]:
% 0.21/0.50                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                         ( ( ( D ) = ( E ) ) =>
% 0.21/0.50                           ( ( k8_relset_1 @
% 0.21/0.50                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.50                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.21/0.50                             ( k2_pre_topc @
% 0.21/0.50                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.21/0.50                ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.50                    ( v1_funct_2 @
% 0.21/0.50                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.50                    ( m1_subset_1 @
% 0.21/0.50                      C @ 
% 0.21/0.50                      ( k1_zfmisc_1 @
% 0.21/0.50                        ( k2_zfmisc_1 @
% 0.21/0.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.21/0.50                    ( ![D:$i]:
% 0.21/0.50                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                        ( ![E:$i]:
% 0.21/0.50                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                            ( ( ( D ) = ( E ) ) =>
% 0.21/0.50                              ( ( k8_relset_1 @
% 0.21/0.50                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.50                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.21/0.50                                ( k2_pre_topc @
% 0.21/0.50                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain, (((sk_D) = (sk_E))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X5)
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ X5)
% 0.21/0.50          | ((k6_domain_1 @ X5 @ X6) = (k1_tarski @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('7', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(dt_k1_tex_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.51         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.51         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.51          | (m1_pre_topc @ (k1_tex_2 @ X12 @ X13) @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D) @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t1_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( m1_subset_1 @
% 0.21/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.51          | (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_pre_topc @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_D)) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_D)) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.51          | (v1_pre_topc @ (k1_tex_2 @ X12 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf(d4_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.21/0.51                 ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.21/0.51                 ( ( u1_struct_0 @ C ) =
% 0.21/0.51                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.51          | ((X11) != (k1_tex_2 @ X10 @ X9))
% 0.21/0.51          | ((u1_struct_0 @ X11) = (k6_domain_1 @ (u1_struct_0 @ X10) @ X9))
% 0.21/0.51          | ~ (m1_pre_topc @ X11 @ X10)
% 0.21/0.51          | ~ (v1_pre_topc @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | ~ (l1_pre_topc @ X10)
% 0.21/0.51          | (v2_struct_0 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X10)
% 0.21/0.51          | ~ (l1_pre_topc @ X10)
% 0.21/0.51          | (v2_struct_0 @ (k1_tex_2 @ X10 @ X9))
% 0.21/0.51          | ~ (v1_pre_topc @ (k1_tex_2 @ X10 @ X9))
% 0.21/0.51          | ~ (m1_pre_topc @ (k1_tex_2 @ X10 @ X9) @ X10)
% 0.21/0.51          | ((u1_struct_0 @ (k1_tex_2 @ X10 @ X9))
% 0.21/0.51              = (k6_domain_1 @ (u1_struct_0 @ X10) @ X9))
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.21/0.51        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D) @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.51  thf('28', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('29', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_D) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.51  thf('32', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.51          | ~ (v2_struct_0 @ (k1_tex_2 @ X12 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_D)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['31', '38'])).
% 0.21/0.51  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_D))
% 0.21/0.51         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '42'])).
% 0.21/0.51  thf('44', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X5)
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ X5)
% 0.21/0.51          | ((k6_domain_1 @ X5 @ X6) = (k1_tarski @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.51          | (m1_pre_topc @ (k1_tex_2 @ X12 @ X13) @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('52', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '54'])).
% 0.21/0.51  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('57', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.21/0.51      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.51          | (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_pre_topc @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.51          | (v1_pre_topc @ (k1_tex_2 @ X12 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X10)
% 0.21/0.51          | ~ (l1_pre_topc @ X10)
% 0.21/0.51          | (v2_struct_0 @ (k1_tex_2 @ X10 @ X9))
% 0.21/0.51          | ~ (v1_pre_topc @ (k1_tex_2 @ X10 @ X9))
% 0.21/0.51          | ~ (m1_pre_topc @ (k1_tex_2 @ X10 @ X9) @ X10)
% 0.21/0.51          | ((u1_struct_0 @ (k1_tex_2 @ X10 @ X9))
% 0.21/0.51              = (k6_domain_1 @ (u1_struct_0 @ X10) @ X9))
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.51        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('72', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_B @ sk_D) @ sk_B)),
% 0.21/0.51      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      ((((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51          = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.21/0.51  thf('75', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.51          | ~ (v2_struct_0 @ (k1_tex_2 @ X12 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D)) | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.51  thf('80', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('81', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['79', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['74', '81'])).
% 0.21/0.51  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (((u1_struct_0 @ (k1_tex_2 @ sk_B @ sk_D))
% 0.21/0.51         = (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['46', '85'])).
% 0.21/0.51  thf('87', plain,
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
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X14)
% 0.21/0.51          | ~ (v4_tex_2 @ X14 @ X15)
% 0.21/0.51          | ~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.51          | ~ (v3_borsuk_1 @ X16 @ X15 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | ((X17) != (X18))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14) @ X16 @ 
% 0.21/0.51              X17) = (k2_pre_topc @ X15 @ X18))
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.21/0.51          | ~ (v5_pre_topc @ X16 @ X15 @ X14)
% 0.21/0.51          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.51          | ~ (v1_funct_1 @ X16)
% 0.21/0.51          | ~ (l1_pre_topc @ X15)
% 0.21/0.51          | ~ (v3_tdlat_3 @ X15)
% 0.21/0.51          | ~ (v2_pre_topc @ X15)
% 0.21/0.51          | (v2_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X15)
% 0.21/0.51          | ~ (v2_pre_topc @ X15)
% 0.21/0.51          | ~ (v3_tdlat_3 @ X15)
% 0.21/0.51          | ~ (l1_pre_topc @ X15)
% 0.21/0.51          | ~ (v1_funct_1 @ X16)
% 0.21/0.51          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.51          | ~ (v5_pre_topc @ X16 @ X15 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14) @ X16 @ 
% 0.21/0.51              X18) = (k2_pre_topc @ X15 @ X18))
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | ~ (v3_borsuk_1 @ X16 @ X15 @ X14)
% 0.21/0.51          | ~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.51          | ~ (v4_tex_2 @ X14 @ X15)
% 0.21/0.51          | (v2_struct_0 @ X14))),
% 0.21/0.51      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.51  thf('90', plain,
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
% 0.21/0.51      inference('sup-', [status(thm)], ['87', '89'])).
% 0.21/0.51  thf('91', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('92', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('93', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('94', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('98', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['90', '91', '92', '93', '94', '95', '96', '97', '98', '99'])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['86', '100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '101'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('105', plain, (((sk_D) = (sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('106', plain,
% 0.21/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['104', '105'])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51          (k1_tarski @ sk_D))
% 0.21/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['103', '106'])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.21/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['102', '107'])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.21/0.51            != (k2_pre_topc @ sk_A @ 
% 0.21/0.51                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['108'])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.21/0.51          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['110'])).
% 0.21/0.51  thf(fc2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (l1_struct_0 @ X4)
% 0.21/0.51          | (v2_struct_0 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['111', '112'])).
% 0.21/0.51  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('115', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['114', '115'])).
% 0.21/0.51  thf('117', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['113', '116'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['117'])).
% 0.21/0.51  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('120', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['118', '119'])).
% 0.21/0.51  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('122', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['120', '121'])).
% 0.21/0.51  thf('123', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (l1_struct_0 @ X4)
% 0.21/0.51          | (v2_struct_0 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('124', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.51  thf('125', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('126', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.51  thf('128', plain, ((v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['124', '127'])).
% 0.21/0.51  thf('129', plain, ($false), inference('demod', [status(thm)], ['0', '128'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
