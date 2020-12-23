%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vQFkaVPyY0

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:50 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 411 expanded)
%              Number of leaves         :   40 ( 137 expanded)
%              Depth                    :   24
%              Number of atoms          : 1219 (11597 expanded)
%              Number of equality atoms :   31 ( 315 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
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
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_xboole_0 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v3_tex_2 @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X47 @ X48 )
      | ~ ( v4_tex_2 @ X47 @ X48 )
      | ( X49
       != ( u1_struct_0 @ X47 ) )
      | ( v3_tex_2 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('14',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X47 ) @ X48 )
      | ~ ( v4_tex_2 @ X47 @ X48 )
      | ~ ( m1_pre_topc @ X47 @ X48 ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_D ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_D ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tarski @ ( k1_tarski @ sk_D ) @ X0 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( v2_struct_0 @ X52 )
      | ~ ( v4_tex_2 @ X52 @ X53 )
      | ~ ( m1_pre_topc @ X52 @ X53 )
      | ~ ( v3_borsuk_1 @ X54 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( X55 != X56 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X53 ) @ ( u1_struct_0 @ X52 ) @ X54 @ X55 )
        = ( k2_pre_topc @ X53 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X53 ) @ ( u1_struct_0 @ X52 ) ) ) )
      | ~ ( v5_pre_topc @ X54 @ X53 @ X52 )
      | ~ ( v1_funct_2 @ X54 @ ( u1_struct_0 @ X53 ) @ ( u1_struct_0 @ X52 ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v3_tdlat_3 @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('65',plain,(
    ! [X52: $i,X53: $i,X54: $i,X56: $i] :
      ( ( v2_struct_0 @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ~ ( v3_tdlat_3 @ X53 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ ( u1_struct_0 @ X53 ) @ ( u1_struct_0 @ X52 ) )
      | ~ ( v5_pre_topc @ X54 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X53 ) @ ( u1_struct_0 @ X52 ) ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X53 ) @ ( u1_struct_0 @ X52 ) @ X54 @ X56 )
        = ( k2_pre_topc @ X53 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v3_borsuk_1 @ X54 @ X53 @ X52 )
      | ~ ( m1_pre_topc @ X52 @ X53 )
      | ~ ( v4_tex_2 @ X52 @ X53 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
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
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72','73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['77','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('92',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','92'])).

thf('94',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['22','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vQFkaVPyY0
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.55/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.78  % Solved by: fo/fo7.sh
% 0.55/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.78  % done 647 iterations in 0.356s
% 0.55/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.78  % SZS output start Refutation
% 0.55/0.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.78  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.55/0.78  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.55/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.78  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.55/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.78  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.55/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.78  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.55/0.78  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.55/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.78  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.55/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.78  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.55/0.78  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.55/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.78  thf(sk_E_type, type, sk_E: $i).
% 0.55/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.55/0.78  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.55/0.78  thf(t77_tex_2, conjecture,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.55/0.78         ( l1_pre_topc @ A ) ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.55/0.78             ( m1_pre_topc @ B @ A ) ) =>
% 0.55/0.78           ( ![C:$i]:
% 0.55/0.78             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.78                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.78                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.55/0.78                 ( m1_subset_1 @
% 0.55/0.78                   C @ 
% 0.55/0.78                   ( k1_zfmisc_1 @
% 0.55/0.78                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.78               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.55/0.78                 ( ![D:$i]:
% 0.55/0.78                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.55/0.78                     ( ![E:$i]:
% 0.55/0.78                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.78                         ( ( ( D ) = ( E ) ) =>
% 0.55/0.78                           ( ( k8_relset_1 @
% 0.55/0.78                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.55/0.78                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.55/0.78                             ( k2_pre_topc @
% 0.55/0.78                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.78    (~( ![A:$i]:
% 0.55/0.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.55/0.78            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.78          ( ![B:$i]:
% 0.55/0.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.55/0.78                ( m1_pre_topc @ B @ A ) ) =>
% 0.55/0.78              ( ![C:$i]:
% 0.55/0.78                ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.78                    ( v1_funct_2 @
% 0.55/0.78                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.78                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.55/0.78                    ( m1_subset_1 @
% 0.55/0.78                      C @ 
% 0.55/0.78                      ( k1_zfmisc_1 @
% 0.55/0.78                        ( k2_zfmisc_1 @
% 0.55/0.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.78                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.55/0.78                    ( ![D:$i]:
% 0.55/0.78                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.55/0.78                        ( ![E:$i]:
% 0.55/0.78                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.78                            ( ( ( D ) = ( E ) ) =>
% 0.55/0.78                              ( ( k8_relset_1 @
% 0.55/0.78                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.78                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.55/0.78                                ( k2_pre_topc @
% 0.55/0.78                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.55/0.78    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.55/0.78  thf('0', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t1_tsep_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( l1_pre_topc @ A ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.78           ( m1_subset_1 @
% 0.55/0.78             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.55/0.78  thf('1', plain,
% 0.55/0.78      (![X45 : $i, X46 : $i]:
% 0.55/0.78         (~ (m1_pre_topc @ X45 @ X46)
% 0.55/0.78          | (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.55/0.78             (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.55/0.78          | ~ (l1_pre_topc @ X46))),
% 0.55/0.78      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.55/0.78  thf('2', plain,
% 0.55/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.78        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.78  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('4', plain,
% 0.55/0.78      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('demod', [status(thm)], ['2', '3'])).
% 0.55/0.78  thf(t46_tex_2, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( ( v1_xboole_0 @ B ) & 
% 0.55/0.78             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.78           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.55/0.78  thf('5', plain,
% 0.55/0.78      (![X50 : $i, X51 : $i]:
% 0.55/0.78         (~ (v1_xboole_0 @ X50)
% 0.55/0.78          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.55/0.78          | ~ (v3_tex_2 @ X50 @ X51)
% 0.55/0.78          | ~ (l1_pre_topc @ X51)
% 0.55/0.78          | ~ (v2_pre_topc @ X51)
% 0.55/0.78          | (v2_struct_0 @ X51))),
% 0.55/0.78      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.55/0.78  thf('6', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_A)
% 0.55/0.78        | ~ (v2_pre_topc @ sk_A)
% 0.55/0.78        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.78        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.55/0.78        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.78  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('9', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_A)
% 0.55/0.78        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.55/0.78        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.55/0.78  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('11', plain,
% 0.55/0.78      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.55/0.78      inference('clc', [status(thm)], ['9', '10'])).
% 0.55/0.78  thf('12', plain,
% 0.55/0.78      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('demod', [status(thm)], ['2', '3'])).
% 0.55/0.78  thf(d8_tex_2, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.78           ( ( v4_tex_2 @ B @ A ) <=>
% 0.55/0.78             ( ![C:$i]:
% 0.55/0.78               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.78                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.55/0.78  thf('13', plain,
% 0.55/0.78      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.55/0.78         (~ (m1_pre_topc @ X47 @ X48)
% 0.55/0.78          | ~ (v4_tex_2 @ X47 @ X48)
% 0.55/0.78          | ((X49) != (u1_struct_0 @ X47))
% 0.55/0.78          | (v3_tex_2 @ X49 @ X48)
% 0.55/0.78          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.55/0.78          | ~ (l1_pre_topc @ X48)
% 0.55/0.78          | (v2_struct_0 @ X48))),
% 0.55/0.78      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.55/0.78  thf('14', plain,
% 0.55/0.78      (![X47 : $i, X48 : $i]:
% 0.55/0.78         ((v2_struct_0 @ X48)
% 0.55/0.78          | ~ (l1_pre_topc @ X48)
% 0.55/0.78          | ~ (m1_subset_1 @ (u1_struct_0 @ X47) @ 
% 0.55/0.78               (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.55/0.78          | (v3_tex_2 @ (u1_struct_0 @ X47) @ X48)
% 0.55/0.78          | ~ (v4_tex_2 @ X47 @ X48)
% 0.55/0.78          | ~ (m1_pre_topc @ X47 @ X48))),
% 0.55/0.78      inference('simplify', [status(thm)], ['13'])).
% 0.55/0.78  thf('15', plain,
% 0.55/0.78      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.55/0.78        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.55/0.78        | (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.55/0.78        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.78        | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['12', '14'])).
% 0.55/0.78  thf('16', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('17', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('19', plain,
% 0.55/0.78      (((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.55/0.78  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('21', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.55/0.78      inference('clc', [status(thm)], ['19', '20'])).
% 0.55/0.78  thf('22', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['11', '21'])).
% 0.55/0.78  thf(d1_xboole_0, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.55/0.78  thf('23', plain,
% 0.55/0.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.55/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.78  thf('24', plain,
% 0.55/0.78      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('demod', [status(thm)], ['2', '3'])).
% 0.55/0.78  thf(t3_subset, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.78  thf('25', plain,
% 0.55/0.78      (![X35 : $i, X36 : $i]:
% 0.55/0.78         ((r1_tarski @ X35 @ X36) | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.78  thf('26', plain,
% 0.55/0.78      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.78  thf(d3_tarski, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.55/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.55/0.78  thf('27', plain,
% 0.55/0.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X3 @ X4)
% 0.55/0.78          | (r2_hidden @ X3 @ X5)
% 0.55/0.78          | ~ (r1_tarski @ X4 @ X5))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.78  thf('28', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.78          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.55/0.78  thf('29', plain,
% 0.55/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78        | (r2_hidden @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['23', '28'])).
% 0.55/0.78  thf('30', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.78  thf('31', plain,
% 0.55/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['29', '30'])).
% 0.55/0.78  thf('32', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('33', plain, (((sk_D) = (sk_E))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('34', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.55/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.55/0.78  thf(redefinition_k6_domain_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.55/0.78       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.55/0.78  thf('35', plain,
% 0.55/0.78      (![X43 : $i, X44 : $i]:
% 0.55/0.78         ((v1_xboole_0 @ X43)
% 0.55/0.78          | ~ (m1_subset_1 @ X44 @ X43)
% 0.55/0.78          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 0.55/0.78      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.55/0.78  thf('36', plain,
% 0.55/0.78      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.78  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('38', plain,
% 0.55/0.78      (![X43 : $i, X44 : $i]:
% 0.55/0.78         ((v1_xboole_0 @ X43)
% 0.55/0.78          | ~ (m1_subset_1 @ X44 @ X43)
% 0.55/0.78          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 0.55/0.78      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.55/0.78  thf('39', plain,
% 0.55/0.78      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.78  thf('40', plain,
% 0.55/0.78      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.55/0.78         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('41', plain, (((sk_D) = (sk_E))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('42', plain,
% 0.55/0.78      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.55/0.78         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.55/0.78      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.78  thf('43', plain,
% 0.55/0.78      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78          sk_C_2 @ (k1_tarski @ sk_D))
% 0.55/0.78          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['39', '42'])).
% 0.55/0.78  thf('44', plain,
% 0.55/0.78      (![X4 : $i, X6 : $i]:
% 0.55/0.78         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.78  thf('45', plain,
% 0.55/0.78      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.78  thf('46', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(dt_k6_domain_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.55/0.78       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.55/0.78  thf('47', plain,
% 0.55/0.78      (![X41 : $i, X42 : $i]:
% 0.55/0.78         ((v1_xboole_0 @ X41)
% 0.55/0.78          | ~ (m1_subset_1 @ X42 @ X41)
% 0.55/0.78          | (m1_subset_1 @ (k6_domain_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41)))),
% 0.55/0.78      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.55/0.78  thf('48', plain,
% 0.55/0.78      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.55/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.78  thf('49', plain,
% 0.55/0.78      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.55/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['45', '48'])).
% 0.55/0.78  thf('50', plain,
% 0.55/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.55/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['49'])).
% 0.55/0.78  thf('51', plain,
% 0.55/0.78      (![X35 : $i, X36 : $i]:
% 0.55/0.78         ((r1_tarski @ X35 @ X36) | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.78  thf('52', plain,
% 0.55/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.78  thf('53', plain,
% 0.55/0.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X3 @ X4)
% 0.55/0.78          | (r2_hidden @ X3 @ X5)
% 0.55/0.78          | ~ (r1_tarski @ X4 @ X5))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.78  thf('54', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_D)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.78  thf('55', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((r1_tarski @ (k1_tarski @ sk_D) @ X0)
% 0.55/0.78          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_D)) @ 
% 0.55/0.78             (u1_struct_0 @ sk_B_1))
% 0.55/0.78          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['44', '54'])).
% 0.55/0.78  thf('56', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['11', '21'])).
% 0.55/0.78  thf('57', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_D)) @ 
% 0.55/0.78           (u1_struct_0 @ sk_B_1))
% 0.55/0.78          | (r1_tarski @ (k1_tarski @ sk_D) @ X0))),
% 0.55/0.78      inference('clc', [status(thm)], ['55', '56'])).
% 0.55/0.78  thf('58', plain,
% 0.55/0.78      (![X4 : $i, X6 : $i]:
% 0.55/0.78         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.78  thf('59', plain,
% 0.55/0.78      (((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 0.55/0.78        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.78  thf('60', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('simplify', [status(thm)], ['59'])).
% 0.55/0.78  thf('61', plain,
% 0.55/0.78      (![X35 : $i, X37 : $i]:
% 0.55/0.78         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 0.55/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.78  thf('62', plain,
% 0.55/0.78      ((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.55/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.55/0.78  thf('63', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C_2 @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t76_tex_2, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.55/0.78         ( l1_pre_topc @ A ) ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.55/0.78             ( m1_pre_topc @ B @ A ) ) =>
% 0.55/0.78           ( ![C:$i]:
% 0.55/0.78             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.78                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.78                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.55/0.78                 ( m1_subset_1 @
% 0.55/0.78                   C @ 
% 0.55/0.78                   ( k1_zfmisc_1 @
% 0.55/0.78                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.78               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.55/0.78                 ( ![D:$i]:
% 0.55/0.78                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.55/0.78                     ( ![E:$i]:
% 0.55/0.78                       ( ( m1_subset_1 @
% 0.55/0.78                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.78                         ( ( ( D ) = ( E ) ) =>
% 0.55/0.78                           ( ( k8_relset_1 @
% 0.55/0.78                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.55/0.78                               D ) =
% 0.55/0.78                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.78  thf('64', plain,
% 0.55/0.78      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.55/0.78         ((v2_struct_0 @ X52)
% 0.55/0.78          | ~ (v4_tex_2 @ X52 @ X53)
% 0.55/0.78          | ~ (m1_pre_topc @ X52 @ X53)
% 0.55/0.78          | ~ (v3_borsuk_1 @ X54 @ X53 @ X52)
% 0.55/0.78          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.55/0.78          | ((X55) != (X56))
% 0.55/0.78          | ((k8_relset_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52) @ X54 @ 
% 0.55/0.78              X55) = (k2_pre_topc @ X53 @ X56))
% 0.55/0.78          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.55/0.78          | ~ (m1_subset_1 @ X54 @ 
% 0.55/0.78               (k1_zfmisc_1 @ 
% 0.55/0.78                (k2_zfmisc_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))))
% 0.55/0.78          | ~ (v5_pre_topc @ X54 @ X53 @ X52)
% 0.55/0.78          | ~ (v1_funct_2 @ X54 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))
% 0.55/0.78          | ~ (v1_funct_1 @ X54)
% 0.55/0.78          | ~ (l1_pre_topc @ X53)
% 0.55/0.78          | ~ (v3_tdlat_3 @ X53)
% 0.55/0.78          | ~ (v2_pre_topc @ X53)
% 0.55/0.78          | (v2_struct_0 @ X53))),
% 0.55/0.78      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.55/0.78  thf('65', plain,
% 0.55/0.78      (![X52 : $i, X53 : $i, X54 : $i, X56 : $i]:
% 0.55/0.78         ((v2_struct_0 @ X53)
% 0.55/0.78          | ~ (v2_pre_topc @ X53)
% 0.55/0.78          | ~ (v3_tdlat_3 @ X53)
% 0.55/0.78          | ~ (l1_pre_topc @ X53)
% 0.55/0.78          | ~ (v1_funct_1 @ X54)
% 0.55/0.78          | ~ (v1_funct_2 @ X54 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))
% 0.55/0.78          | ~ (v5_pre_topc @ X54 @ X53 @ X52)
% 0.55/0.78          | ~ (m1_subset_1 @ X54 @ 
% 0.55/0.78               (k1_zfmisc_1 @ 
% 0.55/0.78                (k2_zfmisc_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))))
% 0.55/0.78          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.55/0.78          | ((k8_relset_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52) @ X54 @ 
% 0.55/0.78              X56) = (k2_pre_topc @ X53 @ X56))
% 0.55/0.78          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.55/0.78          | ~ (v3_borsuk_1 @ X54 @ X53 @ X52)
% 0.55/0.78          | ~ (m1_pre_topc @ X52 @ X53)
% 0.55/0.78          | ~ (v4_tex_2 @ X52 @ X53)
% 0.55/0.78          | (v2_struct_0 @ X52))),
% 0.55/0.78      inference('simplify', [status(thm)], ['64'])).
% 0.55/0.78  thf('66', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((v2_struct_0 @ sk_B_1)
% 0.55/0.78          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.55/0.78          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.55/0.78          | ~ (v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.55/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.55/0.78          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78              sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.55/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.78          | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 0.55/0.78          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78               (u1_struct_0 @ sk_B_1))
% 0.55/0.78          | ~ (v1_funct_1 @ sk_C_2)
% 0.55/0.78          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.78          | ~ (v3_tdlat_3 @ sk_A)
% 0.55/0.78          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.78          | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['63', '65'])).
% 0.55/0.78  thf('67', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('68', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('69', plain, ((v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('70', plain, ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('71', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('72', plain, ((v1_funct_1 @ sk_C_2)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('74', plain, ((v3_tdlat_3 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('76', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((v2_struct_0 @ sk_B_1)
% 0.55/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.55/0.78          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78              sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.55/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.78          | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('demod', [status(thm)],
% 0.55/0.78                ['66', '67', '68', '69', '70', '71', '72', '73', '74', '75'])).
% 0.55/0.78  thf('77', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_A)
% 0.55/0.78        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.55/0.78             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.78        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78            sk_C_2 @ (k1_tarski @ sk_D))
% 0.55/0.78            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.55/0.78        | (v2_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['62', '76'])).
% 0.55/0.78  thf('78', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('79', plain,
% 0.55/0.78      ((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.55/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.55/0.78  thf(t39_pre_topc, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( l1_pre_topc @ A ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.78           ( ![C:$i]:
% 0.55/0.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.55/0.78               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.55/0.78  thf('80', plain,
% 0.55/0.78      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.55/0.78         (~ (m1_pre_topc @ X38 @ X39)
% 0.55/0.78          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.55/0.78          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.55/0.78          | ~ (l1_pre_topc @ X39))),
% 0.55/0.78      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.55/0.78  thf('81', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         (~ (l1_pre_topc @ X0)
% 0.55/0.78          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.55/0.78             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.55/0.78          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['79', '80'])).
% 0.55/0.78  thf('82', plain,
% 0.55/0.78      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.55/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.78        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['78', '81'])).
% 0.55/0.78  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('84', plain,
% 0.55/0.78      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('demod', [status(thm)], ['82', '83'])).
% 0.55/0.78  thf('85', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_A)
% 0.55/0.78        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78            sk_C_2 @ (k1_tarski @ sk_D))
% 0.55/0.78            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.55/0.78        | (v2_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['77', '84'])).
% 0.55/0.78  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('87', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_B_1)
% 0.55/0.78        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78            sk_C_2 @ (k1_tarski @ sk_D))
% 0.55/0.78            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.55/0.78      inference('clc', [status(thm)], ['85', '86'])).
% 0.55/0.78  thf('88', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('89', plain,
% 0.55/0.78      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.55/0.78         sk_C_2 @ (k1_tarski @ sk_D))
% 0.55/0.78         = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))),
% 0.55/0.78      inference('clc', [status(thm)], ['87', '88'])).
% 0.55/0.78  thf('90', plain,
% 0.55/0.78      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.55/0.78          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.55/0.78      inference('demod', [status(thm)], ['43', '89'])).
% 0.55/0.78  thf('91', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['11', '21'])).
% 0.55/0.78  thf('92', plain,
% 0.55/0.78      (((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.55/0.78         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.55/0.78      inference('clc', [status(thm)], ['90', '91'])).
% 0.55/0.78  thf('93', plain,
% 0.55/0.78      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.55/0.78          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['36', '92'])).
% 0.55/0.78  thf('94', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.55/0.78      inference('simplify', [status(thm)], ['93'])).
% 0.55/0.78  thf('95', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['31', '94'])).
% 0.55/0.78  thf('96', plain, ($false), inference('demod', [status(thm)], ['22', '95'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.62/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
