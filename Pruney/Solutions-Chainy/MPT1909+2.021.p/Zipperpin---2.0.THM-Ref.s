%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JJuBw5gywQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:49 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 468 expanded)
%              Number of leaves         :   41 ( 154 expanded)
%              Depth                    :   22
%              Number of atoms          : 1230 (13596 expanded)
%              Number of equality atoms :   36 ( 376 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v4_tex_2 @ X24 @ X25 )
      | ( X26
       != ( u1_struct_0 @ X24 ) )
      | ( v3_tex_2 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X24 ) @ X25 )
      | ~ ( v4_tex_2 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('30',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['39','48'])).

thf('50',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('59',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('64',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('68',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_tex_2 @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v3_borsuk_1 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( X32 != X33 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 @ X32 )
        = ( k2_pre_topc @ X30 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v5_pre_topc @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v3_tdlat_3 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('69',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( v3_tdlat_3 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v5_pre_topc @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 @ X33 )
        = ( k2_pre_topc @ X30 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_borsuk_1 @ X31 @ X30 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v4_tex_2 @ X29 @ X30 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('75',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k10_relat_1 @ sk_C_2 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74','75','76','77','78','79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['49','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['22','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JJuBw5gywQ
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 268 iterations in 0.140s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.40/0.59  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.40/0.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.40/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.59  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(t77_tex_2, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.40/0.59         ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.40/0.59             ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.40/0.59                 ( ![D:$i]:
% 0.40/0.59                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.40/0.59                     ( ![E:$i]:
% 0.40/0.59                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.59                         ( ( ( D ) = ( E ) ) =>
% 0.40/0.59                           ( ( k8_relset_1 @
% 0.40/0.59                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.40/0.59                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.40/0.59                             ( k2_pre_topc @
% 0.40/0.59                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.59            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.40/0.59                ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.59              ( ![C:$i]:
% 0.40/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                    ( v1_funct_2 @
% 0.40/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.40/0.59                    ( m1_subset_1 @
% 0.40/0.59                      C @ 
% 0.40/0.59                      ( k1_zfmisc_1 @
% 0.40/0.59                        ( k2_zfmisc_1 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.40/0.59                    ( ![D:$i]:
% 0.40/0.59                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.40/0.59                        ( ![E:$i]:
% 0.40/0.59                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.59                            ( ( ( D ) = ( E ) ) =>
% 0.40/0.59                              ( ( k8_relset_1 @
% 0.40/0.59                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.59                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.40/0.59                                ( k2_pre_topc @
% 0.40/0.59                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.40/0.59  thf('0', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t1_tsep_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.40/0.59           ( m1_subset_1 @
% 0.40/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X22 @ X23)
% 0.40/0.59          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.40/0.59          | ~ (l1_pre_topc @ X23))),
% 0.40/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf(t46_tex_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( v1_xboole_0 @ B ) & 
% 0.40/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.59           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X27 : $i, X28 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ X27)
% 0.40/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.40/0.59          | ~ (v3_tex_2 @ X27 @ X28)
% 0.40/0.59          | ~ (l1_pre_topc @ X28)
% 0.40/0.59          | ~ (v2_pre_topc @ X28)
% 0.40/0.59          | (v2_struct_0 @ X28))),
% 0.40/0.59      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.40/0.59        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.40/0.59        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.40/0.59  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.40/0.59      inference('clc', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf(d8_tex_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.40/0.59           ( ( v4_tex_2 @ B @ A ) <=>
% 0.40/0.59             ( ![C:$i]:
% 0.40/0.59               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X24 @ X25)
% 0.40/0.59          | ~ (v4_tex_2 @ X24 @ X25)
% 0.40/0.59          | ((X26) != (u1_struct_0 @ X24))
% 0.40/0.59          | (v3_tex_2 @ X26 @ X25)
% 0.40/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.40/0.59          | ~ (l1_pre_topc @ X25)
% 0.40/0.59          | (v2_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X24 : $i, X25 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X25)
% 0.40/0.59          | ~ (l1_pre_topc @ X25)
% 0.40/0.59          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.40/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.40/0.59          | (v3_tex_2 @ (u1_struct_0 @ X24) @ X25)
% 0.40/0.59          | ~ (v4_tex_2 @ X24 @ X25)
% 0.40/0.59          | ~ (m1_pre_topc @ X24 @ X25))),
% 0.40/0.59      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.40/0.59        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.40/0.59        | (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['12', '14'])).
% 0.40/0.59  thf('16', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('17', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.40/0.59  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('21', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.40/0.59      inference('clc', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('22', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['11', '21'])).
% 0.40/0.59  thf('23', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('24', plain, (((sk_D) = (sk_E))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('25', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.40/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X20)
% 0.40/0.59          | ~ (m1_subset_1 @ X21 @ X20)
% 0.40/0.59          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.59  thf('28', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X20)
% 0.40/0.59          | ~ (m1_subset_1 @ X21 @ X20)
% 0.40/0.59          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.40/0.59         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('32', plain, (((sk_D) = (sk_E))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.40/0.59         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59          sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C_2 @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k8_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.40/0.59          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59           sk_C_2 @ X0) = (k10_relat_1 @ sk_C_2 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      ((((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('demod', [status(thm)], ['34', '37'])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      ((((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['27', '38'])).
% 0.40/0.59  thf(d1_xboole_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf(t3_subset, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i]:
% 0.40/0.59         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf(d3_tarski, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X3 @ X4)
% 0.40/0.59          | (r2_hidden @ X3 @ X5)
% 0.40/0.59          | ~ (r1_tarski @ X4 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | (r2_hidden @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['40', '45'])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | ((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.40/0.59      inference('clc', [status(thm)], ['39', '48'])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.59  thf('51', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_k6_domain_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.40/0.59       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X18)
% 0.40/0.59          | ~ (m1_subset_1 @ X19 @ X18)
% 0.40/0.59          | (m1_subset_1 @ (k6_domain_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18)))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.40/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i]:
% 0.40/0.59         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.40/0.59           (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X8 : $i, X10 : $i]:
% 0.40/0.59         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.59  thf('58', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['11', '21'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('clc', [status(thm)], ['57', '58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i]:
% 0.40/0.59         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      ((r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.40/0.59        (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      (((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['50', '61'])).
% 0.40/0.59  thf('63', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['11', '21'])).
% 0.40/0.59  thf('64', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('clc', [status(thm)], ['62', '63'])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      (![X8 : $i, X10 : $i]:
% 0.40/0.59         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('66', plain,
% 0.40/0.59      ((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.59  thf('67', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C_2 @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t76_tex_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.40/0.59         ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.40/0.59             ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.40/0.59                 ( ![D:$i]:
% 0.40/0.59                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.40/0.59                     ( ![E:$i]:
% 0.40/0.59                       ( ( m1_subset_1 @
% 0.40/0.59                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59                         ( ( ( D ) = ( E ) ) =>
% 0.40/0.59                           ( ( k8_relset_1 @
% 0.40/0.59                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.40/0.59                               D ) =
% 0.40/0.59                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X29)
% 0.40/0.59          | ~ (v4_tex_2 @ X29 @ X30)
% 0.40/0.59          | ~ (m1_pre_topc @ X29 @ X30)
% 0.40/0.59          | ~ (v3_borsuk_1 @ X31 @ X30 @ X29)
% 0.40/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.40/0.59          | ((X32) != (X33))
% 0.40/0.59          | ((k8_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31 @ 
% 0.40/0.59              X32) = (k2_pre_topc @ X30 @ X33))
% 0.40/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.40/0.59          | ~ (m1_subset_1 @ X31 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.40/0.59          | ~ (v5_pre_topc @ X31 @ X30 @ X29)
% 0.40/0.59          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.40/0.59          | ~ (v1_funct_1 @ X31)
% 0.40/0.59          | ~ (l1_pre_topc @ X30)
% 0.40/0.59          | ~ (v3_tdlat_3 @ X30)
% 0.40/0.59          | ~ (v2_pre_topc @ X30)
% 0.40/0.59          | (v2_struct_0 @ X30))),
% 0.40/0.59      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X30)
% 0.40/0.59          | ~ (v2_pre_topc @ X30)
% 0.40/0.59          | ~ (v3_tdlat_3 @ X30)
% 0.40/0.59          | ~ (l1_pre_topc @ X30)
% 0.40/0.59          | ~ (v1_funct_1 @ X31)
% 0.40/0.59          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.40/0.59          | ~ (v5_pre_topc @ X31 @ X30 @ X29)
% 0.40/0.59          | ~ (m1_subset_1 @ X31 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.40/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.40/0.59          | ((k8_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31 @ 
% 0.40/0.59              X33) = (k2_pre_topc @ X30 @ X33))
% 0.40/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.40/0.59          | ~ (v3_borsuk_1 @ X31 @ X30 @ X29)
% 0.40/0.59          | ~ (m1_pre_topc @ X29 @ X30)
% 0.40/0.59          | ~ (v4_tex_2 @ X29 @ X30)
% 0.40/0.59          | (v2_struct_0 @ X29))),
% 0.40/0.59      inference('simplify', [status(thm)], ['68'])).
% 0.40/0.59  thf('70', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v2_struct_0 @ sk_B_1)
% 0.40/0.59          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.40/0.59          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.40/0.59          | ~ (v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.40/0.59          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59              sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59          | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 0.40/0.59          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59               (u1_struct_0 @ sk_B_1))
% 0.40/0.59          | ~ (v1_funct_1 @ sk_C_2)
% 0.40/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.59          | ~ (v3_tdlat_3 @ sk_A)
% 0.40/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.59          | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['67', '69'])).
% 0.40/0.59  thf('71', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('72', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('73', plain, ((v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.40/0.59           sk_C_2 @ X0) = (k10_relat_1 @ sk_C_2 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('75', plain, ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('77', plain, ((v1_funct_1 @ sk_C_2)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('79', plain, ((v3_tdlat_3 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('81', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v2_struct_0 @ sk_B_1)
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.40/0.59          | ((k10_relat_1 @ sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59          | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['70', '71', '72', '73', '74', '75', '76', '77', '78', '79', 
% 0.40/0.59                 '80'])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59        | ((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.40/0.59        | (v2_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['66', '81'])).
% 0.40/0.59  thf('83', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('84', plain,
% 0.40/0.59      ((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.59  thf(t39_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.40/0.59               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X15 @ X16)
% 0.40/0.59          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.40/0.59          | ~ (l1_pre_topc @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.40/0.59  thf('86', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X0)
% 0.40/0.59          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.59          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['84', '85'])).
% 0.40/0.59  thf('87', plain,
% 0.40/0.59      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.40/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['83', '86'])).
% 0.40/0.59  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('89', plain,
% 0.40/0.59      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['87', '88'])).
% 0.40/0.59  thf('90', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.40/0.59        | (v2_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['82', '89'])).
% 0.40/0.59  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('92', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B_1)
% 0.40/0.59        | ((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.40/0.59      inference('clc', [status(thm)], ['90', '91'])).
% 0.40/0.59  thf('93', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('94', plain,
% 0.40/0.59      (((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59         = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))),
% 0.40/0.59      inference('clc', [status(thm)], ['92', '93'])).
% 0.40/0.59  thf('95', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.40/0.59        | ((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.40/0.59            != (k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D))))),
% 0.40/0.59      inference('demod', [status(thm)], ['49', '94'])).
% 0.40/0.59  thf('96', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.40/0.59      inference('simplify', [status(thm)], ['95'])).
% 0.40/0.59  thf('97', plain, ($false), inference('demod', [status(thm)], ['22', '96'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
