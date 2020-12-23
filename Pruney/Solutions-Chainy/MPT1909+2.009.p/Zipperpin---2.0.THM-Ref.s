%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q8p2jb0mGh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:47 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 488 expanded)
%              Number of leaves         :   40 ( 162 expanded)
%              Depth                    :   19
%              Number of atoms          : 1131 (12760 expanded)
%              Number of equality atoms :   28 ( 333 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ X52 ) )
      | ( r2_hidden @ X51 @ ( k1_connsp_2 @ X52 @ X51 ) )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( l1_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( u1_struct_0 @ X49 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X49 @ X50 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( k1_connsp_2 @ sk_B @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_pre_topc @ X44 @ X45 )
      | ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('48',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('54',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ X47 )
      | ( ( k6_domain_1 @ X47 @ X48 )
        = ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('55',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ X47 )
      | ( ( k6_domain_1 @ X47 @ X48 )
        = ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('58',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X32 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('65',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( v2_struct_0 @ X53 )
      | ~ ( v4_tex_2 @ X53 @ X54 )
      | ~ ( m1_pre_topc @ X53 @ X54 )
      | ~ ( v3_borsuk_1 @ X55 @ X54 @ X53 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( X56 != X57 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X53 ) @ X55 @ X56 )
        = ( k2_pre_topc @ X54 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X53 ) ) ) )
      | ~ ( v5_pre_topc @ X55 @ X54 @ X53 )
      | ~ ( v1_funct_2 @ X55 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X53 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v3_tdlat_3 @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ( v2_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('68',plain,(
    ! [X53: $i,X54: $i,X55: $i,X57: $i] :
      ( ( v2_struct_0 @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ~ ( v3_tdlat_3 @ X54 )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X53 ) )
      | ~ ( v5_pre_topc @ X55 @ X54 @ X53 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X53 ) ) ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X53 ) @ X55 @ X57 )
        = ( k2_pre_topc @ X54 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v3_borsuk_1 @ X55 @ X54 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X54 )
      | ~ ( v4_tex_2 @ X53 @ X54 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
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
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C_1 ),
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
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','79'])).

thf('81',plain,(
    r2_hidden @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','45'])).

thf('82',plain,(
    ! [X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X32 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('83',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','88'])).

thf('90',plain,(
    r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['89','92'])).

thf('94',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','93'])).

thf('95',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['50','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q8p2jb0mGh
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 287 iterations in 0.209s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.63  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.46/0.63  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.46/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.46/0.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(t77_tex_2, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.63         ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.63             ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.63                 ( m1_subset_1 @
% 0.46/0.63                   C @ 
% 0.46/0.63                   ( k1_zfmisc_1 @
% 0.46/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.63                 ( ![D:$i]:
% 0.46/0.63                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.63                     ( ![E:$i]:
% 0.46/0.63                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63                         ( ( ( D ) = ( E ) ) =>
% 0.46/0.63                           ( ( k8_relset_1 @
% 0.46/0.63                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.63                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.46/0.63                             ( k2_pre_topc @
% 0.46/0.63                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.63                ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.63              ( ![C:$i]:
% 0.46/0.63                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                    ( v1_funct_2 @
% 0.46/0.63                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.63                    ( m1_subset_1 @
% 0.46/0.63                      C @ 
% 0.46/0.63                      ( k1_zfmisc_1 @
% 0.46/0.63                        ( k2_zfmisc_1 @
% 0.46/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.63                    ( ![D:$i]:
% 0.46/0.63                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.63                        ( ![E:$i]:
% 0.46/0.63                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63                            ( ( ( D ) = ( E ) ) =>
% 0.46/0.63                              ( ( k8_relset_1 @
% 0.46/0.63                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.63                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.46/0.63                                ( k2_pre_topc @
% 0.46/0.63                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.46/0.63  thf('0', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t30_connsp_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X51 : $i, X52 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X51 @ (u1_struct_0 @ X52))
% 0.46/0.63          | (r2_hidden @ X51 @ (k1_connsp_2 @ X52 @ X51))
% 0.46/0.63          | ~ (l1_pre_topc @ X52)
% 0.46/0.63          | ~ (v2_pre_topc @ X52)
% 0.46/0.63          | (v2_struct_0 @ X52))),
% 0.46/0.63      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_B)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_B)
% 0.46/0.63        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X40 : $i, X41 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X40 @ X41)
% 0.46/0.63          | (v2_pre_topc @ X40)
% 0.46/0.63          | ~ (l1_pre_topc @ X41)
% 0.46/0.63          | ~ (v2_pre_topc @ X41))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.46/0.63  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_m1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X42 : $i, X43 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X42 @ X43)
% 0.46/0.63          | (l1_pre_topc @ X42)
% 0.46/0.63          | ~ (l1_pre_topc @ X43))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.63  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.63  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B) | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.46/0.63      inference('demod', [status(thm)], ['2', '8', '13'])).
% 0.46/0.63  thf('15', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('16', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_B @ sk_D))),
% 0.46/0.63      inference('clc', [status(thm)], ['14', '15'])).
% 0.46/0.63  thf('17', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k1_connsp_2, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63       ( m1_subset_1 @
% 0.46/0.63         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X49 : $i, X50 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X49)
% 0.46/0.63          | ~ (v2_pre_topc @ X49)
% 0.46/0.63          | (v2_struct_0 @ X49)
% 0.46/0.63          | ~ (m1_subset_1 @ X50 @ (u1_struct_0 @ X49))
% 0.46/0.63          | (m1_subset_1 @ (k1_connsp_2 @ X49 @ X50) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X49))))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.46/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | (v2_struct_0 @ sk_B)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_B)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.46/0.63  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.46/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.46/0.63  thf('23', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      ((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_D) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('clc', [status(thm)], ['22', '23'])).
% 0.46/0.63  thf(t3_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X34 : $i, X35 : $i]:
% 0.46/0.63         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      ((r1_tarski @ (k1_connsp_2 @ sk_B @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.63  thf(d3_tarski, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.63          | (r2_hidden @ X0 @ X2)
% 0.46/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_D)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.63  thf('29', plain, ((r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['16', '28'])).
% 0.46/0.63  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i]:
% 0.46/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i]:
% 0.46/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.63  thf('34', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X34 : $i, X36 : $i]:
% 0.46/0.63         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('36', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf(t39_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.63               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X44 @ X45)
% 0.46/0.63          | (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.46/0.63          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.46/0.63          | ~ (l1_pre_topc @ X45))),
% 0.46/0.63      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X1)
% 0.46/0.63          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.46/0.63          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['30', '38'])).
% 0.46/0.63  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X34 : $i, X35 : $i]:
% 0.46/0.63         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('43', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.63          | (r2_hidden @ X0 @ X2)
% 0.46/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.63          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.63  thf('46', plain, ((r2_hidden @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '45'])).
% 0.46/0.63  thf('47', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf(t5_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.63          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X37 @ X38)
% 0.46/0.63          | ~ (v1_xboole_0 @ X39)
% 0.46/0.63          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.63  thf('50', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['46', '49'])).
% 0.46/0.63  thf('51', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('52', plain, (((sk_D) = (sk_E))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('53', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.63  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.63       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (![X47 : $i, X48 : $i]:
% 0.46/0.63         ((v1_xboole_0 @ X47)
% 0.46/0.63          | ~ (m1_subset_1 @ X48 @ X47)
% 0.46/0.63          | ((k6_domain_1 @ X47 @ X48) = (k1_tarski @ X48)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.63  thf('56', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      (![X47 : $i, X48 : $i]:
% 0.46/0.63         ((v1_xboole_0 @ X47)
% 0.46/0.63          | ~ (m1_subset_1 @ X48 @ X47)
% 0.46/0.63          | ((k6_domain_1 @ X47 @ X48) = (k1_tarski @ X48)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.46/0.63         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.46/0.63         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('60', plain, (((sk_D) = (sk_E))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.46/0.63         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.46/0.63         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.46/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.46/0.63          (k1_tarski @ sk_D))
% 0.46/0.63          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.46/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['58', '61'])).
% 0.46/0.63  thf('63', plain, ((r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['16', '28'])).
% 0.46/0.63  thf(t63_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.63       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (![X32 : $i, X33 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k1_tarski @ X32) @ (k1_zfmisc_1 @ X33))
% 0.46/0.63          | ~ (r2_hidden @ X32 @ X33))),
% 0.46/0.63      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t76_tex_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.63         ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.63             ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.63                 ( m1_subset_1 @
% 0.46/0.63                   C @ 
% 0.46/0.63                   ( k1_zfmisc_1 @
% 0.46/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.63                 ( ![D:$i]:
% 0.46/0.63                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.63                     ( ![E:$i]:
% 0.46/0.63                       ( ( m1_subset_1 @
% 0.46/0.63                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                         ( ( ( D ) = ( E ) ) =>
% 0.46/0.63                           ( ( k8_relset_1 @
% 0.46/0.63                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.63                               D ) =
% 0.46/0.63                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.46/0.63         ((v2_struct_0 @ X53)
% 0.46/0.63          | ~ (v4_tex_2 @ X53 @ X54)
% 0.46/0.63          | ~ (m1_pre_topc @ X53 @ X54)
% 0.46/0.63          | ~ (v3_borsuk_1 @ X55 @ X54 @ X53)
% 0.46/0.63          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.46/0.63          | ((X56) != (X57))
% 0.46/0.63          | ((k8_relset_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X53) @ X55 @ 
% 0.46/0.63              X56) = (k2_pre_topc @ X54 @ X57))
% 0.46/0.63          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.46/0.63          | ~ (m1_subset_1 @ X55 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X53))))
% 0.46/0.63          | ~ (v5_pre_topc @ X55 @ X54 @ X53)
% 0.46/0.63          | ~ (v1_funct_2 @ X55 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X53))
% 0.46/0.63          | ~ (v1_funct_1 @ X55)
% 0.46/0.63          | ~ (l1_pre_topc @ X54)
% 0.46/0.63          | ~ (v3_tdlat_3 @ X54)
% 0.46/0.63          | ~ (v2_pre_topc @ X54)
% 0.46/0.63          | (v2_struct_0 @ X54))),
% 0.46/0.63      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X53 : $i, X54 : $i, X55 : $i, X57 : $i]:
% 0.46/0.63         ((v2_struct_0 @ X54)
% 0.46/0.63          | ~ (v2_pre_topc @ X54)
% 0.46/0.63          | ~ (v3_tdlat_3 @ X54)
% 0.46/0.63          | ~ (l1_pre_topc @ X54)
% 0.46/0.63          | ~ (v1_funct_1 @ X55)
% 0.46/0.63          | ~ (v1_funct_2 @ X55 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X53))
% 0.46/0.63          | ~ (v5_pre_topc @ X55 @ X54 @ X53)
% 0.46/0.63          | ~ (m1_subset_1 @ X55 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X53))))
% 0.46/0.63          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.46/0.63          | ((k8_relset_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X53) @ X55 @ 
% 0.46/0.63              X57) = (k2_pre_topc @ X54 @ X57))
% 0.46/0.63          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.46/0.63          | ~ (v3_borsuk_1 @ X55 @ X54 @ X53)
% 0.46/0.63          | ~ (m1_pre_topc @ X53 @ X54)
% 0.46/0.63          | ~ (v4_tex_2 @ X53 @ X54)
% 0.46/0.63          | (v2_struct_0 @ X53))),
% 0.46/0.63      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_struct_0 @ sk_B)
% 0.46/0.63          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.46/0.63          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.63          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.63          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 0.46/0.63          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63               (u1_struct_0 @ sk_B))
% 0.46/0.63          | ~ (v1_funct_1 @ sk_C_1)
% 0.46/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63          | ~ (v3_tdlat_3 @ sk_A)
% 0.46/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63          | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['66', '68'])).
% 0.46/0.63  thf('70', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('72', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('73', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('75', plain, ((v1_funct_1 @ sk_C_1)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('77', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_struct_0 @ sk_B)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.63          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['69', '70', '71', '72', '73', '74', '75', '76', '77', '78'])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63            sk_C_1 @ (k1_tarski @ sk_D))
% 0.46/0.63            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['65', '79'])).
% 0.46/0.63  thf('81', plain, ((r2_hidden @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '45'])).
% 0.46/0.63  thf('82', plain,
% 0.46/0.63      (![X32 : $i, X33 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k1_tarski @ X32) @ (k1_zfmisc_1 @ X33))
% 0.46/0.63          | ~ (r2_hidden @ X32 @ X33))),
% 0.46/0.63      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.63  thf('84', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63            sk_C_1 @ (k1_tarski @ sk_D))
% 0.46/0.63            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['80', '83'])).
% 0.46/0.63  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('86', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B)
% 0.46/0.63        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63            sk_C_1 @ (k1_tarski @ sk_D))
% 0.46/0.63            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.46/0.63      inference('clc', [status(thm)], ['84', '85'])).
% 0.46/0.63  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('88', plain,
% 0.46/0.63      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.46/0.63         (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))),
% 0.46/0.63      inference('clc', [status(thm)], ['86', '87'])).
% 0.46/0.63  thf('89', plain,
% 0.46/0.63      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.63          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.46/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['62', '88'])).
% 0.46/0.63  thf('90', plain, ((r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['16', '28'])).
% 0.46/0.63  thf('91', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.63  thf('92', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['90', '91'])).
% 0.46/0.63  thf('93', plain,
% 0.46/0.63      (((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.63         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.46/0.63      inference('clc', [status(thm)], ['89', '92'])).
% 0.46/0.63  thf('94', plain,
% 0.46/0.63      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.63          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['55', '93'])).
% 0.46/0.63  thf('95', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('simplify', [status(thm)], ['94'])).
% 0.46/0.63  thf('96', plain, ($false), inference('demod', [status(thm)], ['50', '95'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
