%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZicGouDS5X

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:50 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  156 (1275 expanded)
%              Number of leaves         :   39 ( 381 expanded)
%              Depth                    :   35
%              Number of atoms          : 1359 (38547 expanded)
%              Number of equality atoms :   36 (1049 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    m1_pre_topc @ sk_B @ sk_A ),
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
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('10',plain,(
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

thf('11',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X47 ) @ X48 )
      | ~ ( v4_tex_2 @ X47 @ X48 )
      | ~ ( m1_pre_topc @ X47 @ X48 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r1_tarski @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('33',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('34',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('37',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('49',plain,
    ( ( r2_hidden @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( m1_subset_1 @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('66',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('70',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
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

thf('74',plain,(
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

thf('75',plain,(
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
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
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
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82','83','84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('102',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','102'])).

thf('104',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('106',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['103'])).

thf('109',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['107','108'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( sk_D = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( sk_D
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ sk_D ),
    inference(demod,[status(thm)],['29','112'])).

thf('114',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['21','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZicGouDS5X
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 730 iterations in 0.710s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.01/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.01/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.01/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.01/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.01/1.21  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.01/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.21  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.01/1.21  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.21  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 1.01/1.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.01/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.21  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.01/1.21  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.01/1.21  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.01/1.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.01/1.21  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 1.01/1.21  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 1.01/1.21  thf(sk_E_type, type, sk_E: $i).
% 1.01/1.21  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 1.01/1.21  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.01/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.01/1.21  thf(t77_tex_2, conjecture,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.01/1.21         ( l1_pre_topc @ A ) ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 1.01/1.21             ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.21           ( ![C:$i]:
% 1.01/1.21             ( ( ( v1_funct_1 @ C ) & 
% 1.01/1.21                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.01/1.21                 ( v5_pre_topc @ C @ A @ B ) & 
% 1.01/1.21                 ( m1_subset_1 @
% 1.01/1.21                   C @ 
% 1.01/1.21                   ( k1_zfmisc_1 @
% 1.01/1.21                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.01/1.21               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 1.01/1.21                 ( ![D:$i]:
% 1.01/1.21                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 1.01/1.21                     ( ![E:$i]:
% 1.01/1.21                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 1.01/1.21                         ( ( ( D ) = ( E ) ) =>
% 1.01/1.21                           ( ( k8_relset_1 @
% 1.01/1.21                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.01/1.21                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 1.01/1.21                             ( k2_pre_topc @
% 1.01/1.21                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.21    (~( ![A:$i]:
% 1.01/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.01/1.21            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.21          ( ![B:$i]:
% 1.01/1.21            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 1.01/1.21                ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.21              ( ![C:$i]:
% 1.01/1.21                ( ( ( v1_funct_1 @ C ) & 
% 1.01/1.21                    ( v1_funct_2 @
% 1.01/1.21                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.01/1.21                    ( v5_pre_topc @ C @ A @ B ) & 
% 1.01/1.21                    ( m1_subset_1 @
% 1.01/1.21                      C @ 
% 1.01/1.21                      ( k1_zfmisc_1 @
% 1.01/1.21                        ( k2_zfmisc_1 @
% 1.01/1.21                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.01/1.21                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 1.01/1.21                    ( ![D:$i]:
% 1.01/1.21                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 1.01/1.21                        ( ![E:$i]:
% 1.01/1.21                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 1.01/1.21                            ( ( ( D ) = ( E ) ) =>
% 1.01/1.21                              ( ( k8_relset_1 @
% 1.01/1.21                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.01/1.21                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 1.01/1.21                                ( k2_pre_topc @
% 1.01/1.21                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.01/1.21    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 1.01/1.21  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(t1_tsep_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( l1_pre_topc @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_pre_topc @ B @ A ) =>
% 1.01/1.21           ( m1_subset_1 @
% 1.01/1.21             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.01/1.21  thf('1', plain,
% 1.01/1.21      (![X45 : $i, X46 : $i]:
% 1.01/1.21         (~ (m1_pre_topc @ X45 @ X46)
% 1.01/1.21          | (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 1.01/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.01/1.21          | ~ (l1_pre_topc @ X46))),
% 1.01/1.21      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.01/1.21  thf('2', plain,
% 1.01/1.21      ((~ (l1_pre_topc @ sk_A)
% 1.01/1.21        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['0', '1'])).
% 1.01/1.21  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('4', plain,
% 1.01/1.21      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('demod', [status(thm)], ['2', '3'])).
% 1.01/1.21  thf(t46_tex_2, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( ( v1_xboole_0 @ B ) & 
% 1.01/1.21             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.21           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.01/1.21  thf('5', plain,
% 1.01/1.21      (![X50 : $i, X51 : $i]:
% 1.01/1.21         (~ (v1_xboole_0 @ X50)
% 1.01/1.21          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 1.01/1.21          | ~ (v3_tex_2 @ X50 @ X51)
% 1.01/1.21          | ~ (l1_pre_topc @ X51)
% 1.01/1.21          | ~ (v2_pre_topc @ X51)
% 1.01/1.21          | (v2_struct_0 @ X51))),
% 1.01/1.21      inference('cnf', [status(esa)], [t46_tex_2])).
% 1.01/1.21  thf('6', plain,
% 1.01/1.21      (((v2_struct_0 @ sk_A)
% 1.01/1.21        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.21        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 1.01/1.21        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.21  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('9', plain,
% 1.01/1.21      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('demod', [status(thm)], ['2', '3'])).
% 1.01/1.21  thf(d8_tex_2, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_pre_topc @ B @ A ) =>
% 1.01/1.21           ( ( v4_tex_2 @ B @ A ) <=>
% 1.01/1.21             ( ![C:$i]:
% 1.01/1.21               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf('10', plain,
% 1.01/1.21      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.01/1.21         (~ (m1_pre_topc @ X47 @ X48)
% 1.01/1.21          | ~ (v4_tex_2 @ X47 @ X48)
% 1.01/1.21          | ((X49) != (u1_struct_0 @ X47))
% 1.01/1.21          | (v3_tex_2 @ X49 @ X48)
% 1.01/1.21          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.01/1.21          | ~ (l1_pre_topc @ X48)
% 1.01/1.21          | (v2_struct_0 @ X48))),
% 1.01/1.21      inference('cnf', [status(esa)], [d8_tex_2])).
% 1.01/1.21  thf('11', plain,
% 1.01/1.21      (![X47 : $i, X48 : $i]:
% 1.01/1.21         ((v2_struct_0 @ X48)
% 1.01/1.21          | ~ (l1_pre_topc @ X48)
% 1.01/1.21          | ~ (m1_subset_1 @ (u1_struct_0 @ X47) @ 
% 1.01/1.21               (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.01/1.21          | (v3_tex_2 @ (u1_struct_0 @ X47) @ X48)
% 1.01/1.21          | ~ (v4_tex_2 @ X47 @ X48)
% 1.01/1.21          | ~ (m1_pre_topc @ X47 @ X48))),
% 1.01/1.21      inference('simplify', [status(thm)], ['10'])).
% 1.01/1.21  thf('12', plain,
% 1.01/1.21      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 1.01/1.21        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 1.01/1.21        | (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 1.01/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.21        | (v2_struct_0 @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['9', '11'])).
% 1.01/1.21  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('14', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('16', plain,
% 1.01/1.21      (((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 1.01/1.21      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 1.01/1.21  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('18', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 1.01/1.21      inference('clc', [status(thm)], ['16', '17'])).
% 1.01/1.21  thf('19', plain,
% 1.01/1.21      (((v2_struct_0 @ sk_A) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('demod', [status(thm)], ['6', '7', '8', '18'])).
% 1.01/1.21  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('21', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('clc', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf('22', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(d2_subset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( v1_xboole_0 @ A ) =>
% 1.01/1.21         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.01/1.21       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.01/1.21         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.01/1.21  thf('23', plain,
% 1.01/1.21      (![X30 : $i, X31 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X30 @ X31)
% 1.01/1.21          | (r2_hidden @ X30 @ X31)
% 1.01/1.21          | (v1_xboole_0 @ X31))),
% 1.01/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.01/1.21  thf('24', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['22', '23'])).
% 1.01/1.21  thf(t7_ordinal1, axiom,
% 1.01/1.21    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.01/1.21  thf('25', plain,
% 1.01/1.21      (![X36 : $i, X37 : $i]:
% 1.01/1.21         (~ (r2_hidden @ X36 @ X37) | ~ (r1_tarski @ X37 @ X36))),
% 1.01/1.21      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.01/1.21  thf('26', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ sk_D))),
% 1.01/1.21      inference('sup-', [status(thm)], ['24', '25'])).
% 1.01/1.21  thf('27', plain,
% 1.01/1.21      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('demod', [status(thm)], ['2', '3'])).
% 1.01/1.21  thf(t3_subset, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.01/1.21  thf('28', plain,
% 1.01/1.21      (![X33 : $i, X34 : $i]:
% 1.01/1.21         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('29', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['27', '28'])).
% 1.01/1.21  thf('30', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('31', plain, (((sk_D) = (sk_E))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('32', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 1.01/1.21      inference('demod', [status(thm)], ['30', '31'])).
% 1.01/1.21  thf(redefinition_k6_domain_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.01/1.21       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.01/1.21  thf('33', plain,
% 1.01/1.21      (![X43 : $i, X44 : $i]:
% 1.01/1.21         ((v1_xboole_0 @ X43)
% 1.01/1.21          | ~ (m1_subset_1 @ X44 @ X43)
% 1.01/1.21          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 1.01/1.21      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.01/1.21  thf('34', plain,
% 1.01/1.21      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['32', '33'])).
% 1.01/1.21  thf('35', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('36', plain,
% 1.01/1.21      (![X43 : $i, X44 : $i]:
% 1.01/1.21         ((v1_xboole_0 @ X43)
% 1.01/1.21          | ~ (m1_subset_1 @ X44 @ X43)
% 1.01/1.21          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 1.01/1.21      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.01/1.21  thf('37', plain,
% 1.01/1.21      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['35', '36'])).
% 1.01/1.21  thf('38', plain,
% 1.01/1.21      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 1.01/1.21         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 1.01/1.21         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('39', plain, (((sk_D) = (sk_E))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('40', plain,
% 1.01/1.21      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 1.01/1.21         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 1.01/1.21         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 1.01/1.21      inference('demod', [status(thm)], ['38', '39'])).
% 1.01/1.21  thf('41', plain,
% 1.01/1.21      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 1.01/1.21          (k1_tarski @ sk_D))
% 1.01/1.21          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['37', '40'])).
% 1.01/1.21  thf('42', plain,
% 1.01/1.21      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['35', '36'])).
% 1.01/1.21  thf('43', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(dt_k6_domain_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.01/1.21       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.01/1.21  thf('44', plain,
% 1.01/1.21      (![X41 : $i, X42 : $i]:
% 1.01/1.21         ((v1_xboole_0 @ X41)
% 1.01/1.21          | ~ (m1_subset_1 @ X42 @ X41)
% 1.01/1.21          | (m1_subset_1 @ (k6_domain_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41)))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.01/1.21  thf('45', plain,
% 1.01/1.21      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 1.01/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['43', '44'])).
% 1.01/1.21  thf('46', plain,
% 1.01/1.21      (![X30 : $i, X31 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X30 @ X31)
% 1.01/1.21          | (r2_hidden @ X30 @ X31)
% 1.01/1.21          | (v1_xboole_0 @ X31))),
% 1.01/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.01/1.21  thf('47', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (r2_hidden @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 1.01/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['45', '46'])).
% 1.01/1.21  thf('48', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('clc', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf('49', plain,
% 1.01/1.21      (((r2_hidden @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 1.01/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('clc', [status(thm)], ['47', '48'])).
% 1.01/1.21  thf('50', plain,
% 1.01/1.21      (((r2_hidden @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('sup+', [status(thm)], ['42', '49'])).
% 1.01/1.21  thf('51', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('clc', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf('52', plain,
% 1.01/1.21      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (r2_hidden @ (k1_tarski @ sk_D) @ 
% 1.01/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('clc', [status(thm)], ['50', '51'])).
% 1.01/1.21  thf('53', plain,
% 1.01/1.21      (![X30 : $i, X31 : $i]:
% 1.01/1.21         (~ (r2_hidden @ X30 @ X31)
% 1.01/1.21          | (m1_subset_1 @ X30 @ X31)
% 1.01/1.21          | (v1_xboole_0 @ X31))),
% 1.01/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.01/1.21  thf('54', plain,
% 1.01/1.21      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['52', '53'])).
% 1.01/1.21  thf('55', plain,
% 1.01/1.21      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['54'])).
% 1.01/1.21  thf('56', plain,
% 1.01/1.21      (![X33 : $i, X34 : $i]:
% 1.01/1.21         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('57', plain,
% 1.01/1.21      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['55', '56'])).
% 1.01/1.21  thf('58', plain,
% 1.01/1.21      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['35', '36'])).
% 1.01/1.21  thf('59', plain,
% 1.01/1.21      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 1.01/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['43', '44'])).
% 1.01/1.21  thf('60', plain,
% 1.01/1.21      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['58', '59'])).
% 1.01/1.21  thf('61', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['60'])).
% 1.01/1.21  thf('62', plain,
% 1.01/1.21      (![X31 : $i, X32 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X32 @ X31)
% 1.01/1.21          | (v1_xboole_0 @ X32)
% 1.01/1.21          | ~ (v1_xboole_0 @ X31))),
% 1.01/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.01/1.21  thf('63', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21        | (v1_xboole_0 @ (k1_tarski @ sk_D)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['61', '62'])).
% 1.01/1.21  thf('64', plain,
% 1.01/1.21      (((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (v1_xboole_0 @ (k1_tarski @ sk_D))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['57', '63'])).
% 1.01/1.21  thf('65', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['60'])).
% 1.01/1.21  thf('66', plain,
% 1.01/1.21      (![X33 : $i, X34 : $i]:
% 1.01/1.21         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('67', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['65', '66'])).
% 1.01/1.21  thf('68', plain,
% 1.01/1.21      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.01/1.21        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('clc', [status(thm)], ['64', '67'])).
% 1.01/1.21  thf('69', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('clc', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf('70', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('clc', [status(thm)], ['68', '69'])).
% 1.01/1.21  thf('71', plain,
% 1.01/1.21      (![X33 : $i, X35 : $i]:
% 1.01/1.21         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('72', plain,
% 1.01/1.21      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['70', '71'])).
% 1.01/1.21  thf('73', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C_1 @ 
% 1.01/1.21        (k1_zfmisc_1 @ 
% 1.01/1.21         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(t76_tex_2, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.01/1.21         ( l1_pre_topc @ A ) ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 1.01/1.21             ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.21           ( ![C:$i]:
% 1.01/1.21             ( ( ( v1_funct_1 @ C ) & 
% 1.01/1.21                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.01/1.21                 ( v5_pre_topc @ C @ A @ B ) & 
% 1.01/1.21                 ( m1_subset_1 @
% 1.01/1.21                   C @ 
% 1.01/1.21                   ( k1_zfmisc_1 @
% 1.01/1.21                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.01/1.21               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 1.01/1.21                 ( ![D:$i]:
% 1.01/1.21                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.01/1.21                     ( ![E:$i]:
% 1.01/1.21                       ( ( m1_subset_1 @
% 1.01/1.21                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21                         ( ( ( D ) = ( E ) ) =>
% 1.01/1.21                           ( ( k8_relset_1 @
% 1.01/1.21                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.01/1.21                               D ) =
% 1.01/1.21                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf('74', plain,
% 1.01/1.21      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 1.01/1.21         ((v2_struct_0 @ X52)
% 1.01/1.21          | ~ (v4_tex_2 @ X52 @ X53)
% 1.01/1.21          | ~ (m1_pre_topc @ X52 @ X53)
% 1.01/1.21          | ~ (v3_borsuk_1 @ X54 @ X53 @ X52)
% 1.01/1.21          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.01/1.21          | ((X55) != (X56))
% 1.01/1.21          | ((k8_relset_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52) @ X54 @ 
% 1.01/1.21              X55) = (k2_pre_topc @ X53 @ X56))
% 1.01/1.21          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.01/1.21          | ~ (m1_subset_1 @ X54 @ 
% 1.01/1.21               (k1_zfmisc_1 @ 
% 1.01/1.21                (k2_zfmisc_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))))
% 1.01/1.21          | ~ (v5_pre_topc @ X54 @ X53 @ X52)
% 1.01/1.21          | ~ (v1_funct_2 @ X54 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))
% 1.01/1.21          | ~ (v1_funct_1 @ X54)
% 1.01/1.21          | ~ (l1_pre_topc @ X53)
% 1.01/1.21          | ~ (v3_tdlat_3 @ X53)
% 1.01/1.21          | ~ (v2_pre_topc @ X53)
% 1.01/1.21          | (v2_struct_0 @ X53))),
% 1.01/1.21      inference('cnf', [status(esa)], [t76_tex_2])).
% 1.01/1.21  thf('75', plain,
% 1.01/1.21      (![X52 : $i, X53 : $i, X54 : $i, X56 : $i]:
% 1.01/1.21         ((v2_struct_0 @ X53)
% 1.01/1.21          | ~ (v2_pre_topc @ X53)
% 1.01/1.21          | ~ (v3_tdlat_3 @ X53)
% 1.01/1.21          | ~ (l1_pre_topc @ X53)
% 1.01/1.21          | ~ (v1_funct_1 @ X54)
% 1.01/1.21          | ~ (v1_funct_2 @ X54 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))
% 1.01/1.21          | ~ (v5_pre_topc @ X54 @ X53 @ X52)
% 1.01/1.21          | ~ (m1_subset_1 @ X54 @ 
% 1.01/1.21               (k1_zfmisc_1 @ 
% 1.01/1.21                (k2_zfmisc_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52))))
% 1.01/1.21          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.01/1.21          | ((k8_relset_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X52) @ X54 @ 
% 1.01/1.21              X56) = (k2_pre_topc @ X53 @ X56))
% 1.01/1.21          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.01/1.21          | ~ (v3_borsuk_1 @ X54 @ X53 @ X52)
% 1.01/1.21          | ~ (m1_pre_topc @ X52 @ X53)
% 1.01/1.21          | ~ (v4_tex_2 @ X52 @ X53)
% 1.01/1.21          | (v2_struct_0 @ X52))),
% 1.01/1.21      inference('simplify', [status(thm)], ['74'])).
% 1.01/1.21  thf('76', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((v2_struct_0 @ sk_B)
% 1.01/1.21          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 1.01/1.21          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.01/1.21          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.21          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 1.01/1.21          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.21               (u1_struct_0 @ sk_B))
% 1.01/1.21          | ~ (v1_funct_1 @ sk_C_1)
% 1.01/1.21          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.21          | ~ (v3_tdlat_3 @ sk_A)
% 1.01/1.21          | ~ (v2_pre_topc @ sk_A)
% 1.01/1.21          | (v2_struct_0 @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['73', '75'])).
% 1.01/1.21  thf('77', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('78', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('79', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('80', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('81', plain,
% 1.01/1.21      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('82', plain, ((v1_funct_1 @ sk_C_1)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('84', plain, ((v3_tdlat_3 @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('86', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((v2_struct_0 @ sk_B)
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.01/1.21          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.21          | (v2_struct_0 @ sk_A))),
% 1.01/1.21      inference('demod', [status(thm)],
% 1.01/1.21                ['76', '77', '78', '79', '80', '81', '82', '83', '84', '85'])).
% 1.01/1.21  thf('87', plain,
% 1.01/1.21      (((v2_struct_0 @ sk_A)
% 1.01/1.21        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.21        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21            sk_C_1 @ (k1_tarski @ sk_D))
% 1.01/1.21            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 1.01/1.21        | (v2_struct_0 @ sk_B))),
% 1.01/1.21      inference('sup-', [status(thm)], ['72', '86'])).
% 1.01/1.21  thf('88', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('89', plain,
% 1.01/1.21      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['70', '71'])).
% 1.01/1.21  thf(t39_pre_topc, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( l1_pre_topc @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_pre_topc @ B @ A ) =>
% 1.01/1.21           ( ![C:$i]:
% 1.01/1.21             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.01/1.21               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf('90', plain,
% 1.01/1.21      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.01/1.21         (~ (m1_pre_topc @ X38 @ X39)
% 1.01/1.21          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.01/1.21          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.01/1.21          | ~ (l1_pre_topc @ X39))),
% 1.01/1.21      inference('cnf', [status(esa)], [t39_pre_topc])).
% 1.01/1.21  thf('91', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (~ (l1_pre_topc @ X0)
% 1.01/1.21          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.01/1.21          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['89', '90'])).
% 1.01/1.21  thf('92', plain,
% 1.01/1.21      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.01/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.21        | ~ (l1_pre_topc @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['88', '91'])).
% 1.01/1.21  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('94', plain,
% 1.01/1.21      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('demod', [status(thm)], ['92', '93'])).
% 1.01/1.21  thf('95', plain,
% 1.01/1.21      (((v2_struct_0 @ sk_A)
% 1.01/1.21        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21            sk_C_1 @ (k1_tarski @ sk_D))
% 1.01/1.21            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 1.01/1.21        | (v2_struct_0 @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['87', '94'])).
% 1.01/1.21  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('97', plain,
% 1.01/1.21      (((v2_struct_0 @ sk_B)
% 1.01/1.21        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.01/1.21            sk_C_1 @ (k1_tarski @ sk_D))
% 1.01/1.21            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 1.01/1.21      inference('clc', [status(thm)], ['95', '96'])).
% 1.01/1.21  thf('98', plain, (~ (v2_struct_0 @ sk_B)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('99', plain,
% 1.01/1.21      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 1.01/1.21         (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))),
% 1.01/1.21      inference('clc', [status(thm)], ['97', '98'])).
% 1.01/1.21  thf('100', plain,
% 1.01/1.21      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 1.01/1.21          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.01/1.21      inference('demod', [status(thm)], ['41', '99'])).
% 1.01/1.21  thf('101', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('clc', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf('102', plain,
% 1.01/1.21      (((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 1.01/1.21         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 1.01/1.21      inference('clc', [status(thm)], ['100', '101'])).
% 1.01/1.21  thf('103', plain,
% 1.01/1.21      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 1.01/1.21          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 1.01/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['34', '102'])).
% 1.01/1.21  thf('104', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.01/1.21      inference('simplify', [status(thm)], ['103'])).
% 1.01/1.21  thf('105', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 1.01/1.21      inference('demod', [status(thm)], ['30', '31'])).
% 1.01/1.21  thf('106', plain,
% 1.01/1.21      (![X31 : $i, X32 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X32 @ X31)
% 1.01/1.21          | (v1_xboole_0 @ X32)
% 1.01/1.21          | ~ (v1_xboole_0 @ X31))),
% 1.01/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.01/1.21  thf('107', plain,
% 1.01/1.21      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_D))),
% 1.01/1.21      inference('sup-', [status(thm)], ['105', '106'])).
% 1.01/1.21  thf('108', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.01/1.21      inference('simplify', [status(thm)], ['103'])).
% 1.01/1.21  thf('109', plain, ((v1_xboole_0 @ sk_D)),
% 1.01/1.21      inference('demod', [status(thm)], ['107', '108'])).
% 1.01/1.21  thf(t8_boole, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.01/1.21  thf('110', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t8_boole])).
% 1.01/1.21  thf('111', plain, (![X0 : $i]: (((sk_D) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['109', '110'])).
% 1.01/1.21  thf('112', plain, (((sk_D) = (u1_struct_0 @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['104', '111'])).
% 1.01/1.21  thf('113', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ sk_D)),
% 1.01/1.21      inference('demod', [status(thm)], ['29', '112'])).
% 1.01/1.21  thf('114', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['26', '113'])).
% 1.01/1.21  thf('115', plain, ($false), inference('demod', [status(thm)], ['21', '114'])).
% 1.01/1.21  
% 1.01/1.21  % SZS output end Refutation
% 1.01/1.21  
% 1.01/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
