%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FvYFuKEgcN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 496 expanded)
%              Number of leaves         :   38 ( 158 expanded)
%              Depth                    :   23
%              Number of atoms          : 1225 (15472 expanded)
%              Number of equality atoms :   39 ( 433 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v3_tex_2 @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
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

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ~ ( v4_tex_2 @ X43 @ X44 )
      | ( X45
       != ( u1_struct_0 @ X43 ) )
      | ( v3_tex_2 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('14',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X43 ) @ X44 )
      | ~ ( v4_tex_2 @ X43 @ X44 )
      | ~ ( m1_pre_topc @ X43 @ X44 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('23',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( ( k6_domain_1 @ X36 @ X37 )
        = ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('30',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( ( k6_domain_1 @ X36 @ X37 )
        = ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('33',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X34 @ X33 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ X39 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( ( k7_domain_1 @ X39 @ X38 @ X40 )
        = ( k2_tarski @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k2_tarski @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
    = ( k2_tarski @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('51',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('54',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( v4_tex_2 @ X48 @ X49 )
      | ~ ( m1_pre_topc @ X48 @ X49 )
      | ~ ( v3_borsuk_1 @ X50 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( X51 != X52 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X49 ) @ ( u1_struct_0 @ X48 ) @ X50 @ X51 )
        = ( k2_pre_topc @ X49 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X49 ) @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( v5_pre_topc @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_2 @ X50 @ ( u1_struct_0 @ X49 ) @ ( u1_struct_0 @ X48 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v3_tdlat_3 @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('57',plain,(
    ! [X48: $i,X49: $i,X50: $i,X52: $i] :
      ( ( v2_struct_0 @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ~ ( v3_tdlat_3 @ X49 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ ( u1_struct_0 @ X49 ) @ ( u1_struct_0 @ X48 ) )
      | ~ ( v5_pre_topc @ X50 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X49 ) @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X49 ) @ ( u1_struct_0 @ X48 ) @ X50 @ X52 )
        = ( k2_pre_topc @ X49 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_borsuk_1 @ X50 @ X49 @ X48 )
      | ~ ( m1_pre_topc @ X48 @ X49 )
      | ~ ( v4_tex_2 @ X48 @ X49 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
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
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
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
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64','65','66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('80',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('88',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','88'])).

thf('90',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['22','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FvYFuKEgcN
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 130 iterations in 0.062s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.51  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.19/0.51  thf(k7_domain_1_type, type, k7_domain_1: $i > $i > $i > $i).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.19/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.51  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.19/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(t77_tex_2, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.51         ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.19/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.19/0.51                 ( m1_subset_1 @
% 0.19/0.51                   C @ 
% 0.19/0.51                   ( k1_zfmisc_1 @
% 0.19/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.19/0.51                 ( ![D:$i]:
% 0.19/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.51                     ( ![E:$i]:
% 0.19/0.51                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.19/0.51                           ( ( k8_relset_1 @
% 0.19/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.51                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.19/0.51                             ( k2_pre_topc @
% 0.19/0.51                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.51            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51          ( ![B:$i]:
% 0.19/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.19/0.51                ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51              ( ![C:$i]:
% 0.19/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.51                    ( v1_funct_2 @
% 0.19/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.51                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.19/0.51                    ( m1_subset_1 @
% 0.19/0.51                      C @ 
% 0.19/0.51                      ( k1_zfmisc_1 @
% 0.19/0.51                        ( k2_zfmisc_1 @
% 0.19/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.51                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.19/0.51                    ( ![D:$i]:
% 0.19/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.51                        ( ![E:$i]:
% 0.19/0.51                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51                            ( ( ( D ) = ( E ) ) =>
% 0.19/0.51                              ( ( k8_relset_1 @
% 0.19/0.51                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.51                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.19/0.51                                ( k2_pre_topc @
% 0.19/0.51                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.19/0.51  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t1_tsep_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.51           ( m1_subset_1 @
% 0.19/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X41 : $i, X42 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X41 @ X42)
% 0.19/0.51          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.19/0.51          | ~ (l1_pre_topc @ X42))),
% 0.19/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.51  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf(t46_tex_2, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( v1_xboole_0 @ B ) & 
% 0.19/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.51           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X46 : $i, X47 : $i]:
% 0.19/0.51         (~ (v1_xboole_0 @ X46)
% 0.19/0.51          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.19/0.51          | ~ (v3_tex_2 @ X46 @ X47)
% 0.19/0.51          | ~ (l1_pre_topc @ X47)
% 0.19/0.51          | ~ (v2_pre_topc @ X47)
% 0.19/0.51          | (v2_struct_0 @ X47))),
% 0.19/0.51      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.19/0.51        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.51  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.19/0.51        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.51  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.19/0.51      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf(d8_tex_2, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.51           ( ( v4_tex_2 @ B @ A ) <=>
% 0.19/0.51             ( ![C:$i]:
% 0.19/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X43 @ X44)
% 0.19/0.51          | ~ (v4_tex_2 @ X43 @ X44)
% 0.19/0.51          | ((X45) != (u1_struct_0 @ X43))
% 0.19/0.51          | (v3_tex_2 @ X45 @ X44)
% 0.19/0.51          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.19/0.51          | ~ (l1_pre_topc @ X44)
% 0.19/0.51          | (v2_struct_0 @ X44))),
% 0.19/0.51      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X43 : $i, X44 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X44)
% 0.19/0.51          | ~ (l1_pre_topc @ X44)
% 0.19/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 0.19/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.19/0.51          | (v3_tex_2 @ (u1_struct_0 @ X43) @ X44)
% 0.19/0.51          | ~ (v4_tex_2 @ X43 @ X44)
% 0.19/0.51          | ~ (m1_pre_topc @ X43 @ X44))),
% 0.19/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.19/0.51        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.19/0.51        | (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.19/0.51  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('17', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.19/0.51  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('21', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.19/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.19/0.51  thf('22', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '21'])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf(cc1_subset_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X28 : $i, X29 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.19/0.51          | (v1_xboole_0 @ X28)
% 0.19/0.51          | ~ (v1_xboole_0 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('27', plain, (((sk_D) = (sk_E))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('28', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X36 : $i, X37 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ X36)
% 0.19/0.51          | ~ (m1_subset_1 @ X37 @ X36)
% 0.19/0.51          | ((k6_domain_1 @ X36 @ X37) = (k1_tarski @ X37)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.51  thf('31', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X36 : $i, X37 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ X36)
% 0.19/0.51          | ~ (m1_subset_1 @ X37 @ X36)
% 0.19/0.51          | ((k6_domain_1 @ X36 @ X37) = (k1_tarski @ X37)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.19/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.19/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('35', plain, (((sk_D) = (sk_E))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.19/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.19/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.19/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.19/0.51          (k1_tarski @ sk_D))
% 0.19/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['33', '36'])).
% 0.19/0.51  thf('38', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('39', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_k7_domain_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ C @ A ) ) =>
% 0.19/0.51       ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X33 @ X34)
% 0.19/0.51          | (v1_xboole_0 @ X34)
% 0.19/0.51          | ~ (m1_subset_1 @ X35 @ X34)
% 0.19/0.51          | (m1_subset_1 @ (k7_domain_1 @ X34 @ X33 @ X35) @ 
% 0.19/0.51             (k1_zfmisc_1 @ X34)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k7_domain_1])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ X0) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51        | (m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.19/0.51  thf('43', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('44', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k7_domain_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ C @ A ) ) =>
% 0.19/0.51       ( ( k7_domain_1 @ A @ B @ C ) = ( k2_tarski @ B @ C ) ) ))).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X38 @ X39)
% 0.19/0.51          | (v1_xboole_0 @ X39)
% 0.19/0.51          | ~ (m1_subset_1 @ X40 @ X39)
% 0.19/0.51          | ((k7_domain_1 @ X39 @ X38 @ X40) = (k2_tarski @ X38 @ X40)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k7_domain_1])).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ X0)
% 0.19/0.51            = (k2_tarski @ sk_D @ X0))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.51  thf('47', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '21'])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51          | ((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ X0)
% 0.19/0.51              = (k2_tarski @ sk_D @ X0)))),
% 0.19/0.51      inference('clc', [status(thm)], ['46', '47'])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)
% 0.19/0.51         = (k2_tarski @ sk_D @ sk_D))),
% 0.19/0.51      inference('sup-', [status(thm)], ['43', '48'])).
% 0.19/0.51  thf(t69_enumset1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.51  thf('50', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) = (k1_tarski @ sk_D))),
% 0.19/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.51      inference('demod', [status(thm)], ['42', '51'])).
% 0.19/0.51  thf('53', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '21'])).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('clc', [status(thm)], ['52', '53'])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.51        (k1_zfmisc_1 @ 
% 0.19/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t76_tex_2, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.51         ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.19/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.19/0.51                 ( m1_subset_1 @
% 0.19/0.51                   C @ 
% 0.19/0.51                   ( k1_zfmisc_1 @
% 0.19/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.19/0.51                 ( ![D:$i]:
% 0.19/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.51                     ( ![E:$i]:
% 0.19/0.51                       ( ( m1_subset_1 @
% 0.19/0.51                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.19/0.51                           ( ( k8_relset_1 @
% 0.19/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.51                               D ) =
% 0.19/0.51                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X48)
% 0.19/0.51          | ~ (v4_tex_2 @ X48 @ X49)
% 0.19/0.51          | ~ (m1_pre_topc @ X48 @ X49)
% 0.19/0.51          | ~ (v3_borsuk_1 @ X50 @ X49 @ X48)
% 0.19/0.51          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.19/0.51          | ((X51) != (X52))
% 0.19/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X49) @ (u1_struct_0 @ X48) @ X50 @ 
% 0.19/0.51              X51) = (k2_pre_topc @ X49 @ X52))
% 0.19/0.51          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.19/0.51          | ~ (m1_subset_1 @ X50 @ 
% 0.19/0.51               (k1_zfmisc_1 @ 
% 0.19/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X49) @ (u1_struct_0 @ X48))))
% 0.19/0.51          | ~ (v5_pre_topc @ X50 @ X49 @ X48)
% 0.19/0.51          | ~ (v1_funct_2 @ X50 @ (u1_struct_0 @ X49) @ (u1_struct_0 @ X48))
% 0.19/0.51          | ~ (v1_funct_1 @ X50)
% 0.19/0.51          | ~ (l1_pre_topc @ X49)
% 0.19/0.51          | ~ (v3_tdlat_3 @ X49)
% 0.19/0.51          | ~ (v2_pre_topc @ X49)
% 0.19/0.51          | (v2_struct_0 @ X49))),
% 0.19/0.51      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (![X48 : $i, X49 : $i, X50 : $i, X52 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X49)
% 0.19/0.51          | ~ (v2_pre_topc @ X49)
% 0.19/0.51          | ~ (v3_tdlat_3 @ X49)
% 0.19/0.51          | ~ (l1_pre_topc @ X49)
% 0.19/0.51          | ~ (v1_funct_1 @ X50)
% 0.19/0.51          | ~ (v1_funct_2 @ X50 @ (u1_struct_0 @ X49) @ (u1_struct_0 @ X48))
% 0.19/0.51          | ~ (v5_pre_topc @ X50 @ X49 @ X48)
% 0.19/0.51          | ~ (m1_subset_1 @ X50 @ 
% 0.19/0.51               (k1_zfmisc_1 @ 
% 0.19/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X49) @ (u1_struct_0 @ X48))))
% 0.19/0.51          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.19/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X49) @ (u1_struct_0 @ X48) @ X50 @ 
% 0.19/0.51              X52) = (k2_pre_topc @ X49 @ X52))
% 0.19/0.51          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.19/0.51          | ~ (v3_borsuk_1 @ X50 @ X49 @ X48)
% 0.19/0.51          | ~ (m1_pre_topc @ X48 @ X49)
% 0.19/0.51          | ~ (v4_tex_2 @ X48 @ X49)
% 0.19/0.51          | (v2_struct_0 @ X48))),
% 0.19/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_B)
% 0.19/0.51          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.19/0.51          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 0.19/0.51          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51               (u1_struct_0 @ sk_B))
% 0.19/0.51          | ~ (v1_funct_1 @ sk_C_1)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | ~ (v3_tdlat_3 @ sk_A)
% 0.19/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['55', '57'])).
% 0.19/0.51  thf('59', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('60', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('61', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('62', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('63', plain,
% 0.19/0.51      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('66', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('68', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_B)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)],
% 0.19/0.51                ['58', '59', '60', '61', '62', '63', '64', '65', '66', '67'])).
% 0.19/0.51  thf('69', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.19/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.19/0.51        | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['54', '68'])).
% 0.19/0.51  thf('70', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('71', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51        | (m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.19/0.51  thf(t39_pre_topc, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.51               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('72', plain,
% 0.19/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X30 @ X31)
% 0.19/0.51          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.19/0.51          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.19/0.51          | ~ (l1_pre_topc @ X31))),
% 0.19/0.51      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.19/0.51  thf('73', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.51          | ~ (l1_pre_topc @ X0)
% 0.19/0.51          | (m1_subset_1 @ 
% 0.19/0.51             (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.19/0.51  thf('74', plain,
% 0.19/0.51      (((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.19/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['70', '73'])).
% 0.19/0.51  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('76', plain,
% 0.19/0.51      (((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.19/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['74', '75'])).
% 0.19/0.51  thf('77', plain,
% 0.19/0.51      (((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) = (k1_tarski @ sk_D))),
% 0.19/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.51  thf('78', plain,
% 0.19/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.51  thf('79', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '21'])).
% 0.19/0.51  thf('80', plain,
% 0.19/0.51      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('clc', [status(thm)], ['78', '79'])).
% 0.19/0.51  thf('81', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.19/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.19/0.51        | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['69', '80'])).
% 0.19/0.51  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('83', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_B)
% 0.19/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.19/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.19/0.51      inference('clc', [status(thm)], ['81', '82'])).
% 0.19/0.51  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('85', plain,
% 0.19/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.19/0.51         (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))),
% 0.19/0.51      inference('clc', [status(thm)], ['83', '84'])).
% 0.19/0.51  thf('86', plain,
% 0.19/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.19/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['37', '85'])).
% 0.19/0.51  thf('87', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '21'])).
% 0.19/0.51  thf('88', plain,
% 0.19/0.51      (((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.19/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.19/0.51      inference('clc', [status(thm)], ['86', '87'])).
% 0.19/0.51  thf('89', plain,
% 0.19/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.19/0.51          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['30', '88'])).
% 0.19/0.51  thf('90', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['89'])).
% 0.19/0.51  thf('91', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['25', '90'])).
% 0.19/0.51  thf('92', plain, ($false), inference('demod', [status(thm)], ['22', '91'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
