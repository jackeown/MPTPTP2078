%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aaU60Ej33I

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 280 expanded)
%              Number of leaves         :   32 (  91 expanded)
%              Depth                    :   20
%              Number of atoms          :  963 (3101 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t36_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X16 @ ( k1_connsp_2 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_B_1 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('30',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['32','33'])).

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

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( X20
       != ( k1_tex_2 @ X19 @ X18 ) )
      | ( ( u1_struct_0 @ X20 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X19 @ X18 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X19 @ X18 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X19 @ X18 ) @ X19 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X19 @ X18 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X21 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('41',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('50',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( X27
       != ( u1_struct_0 @ X25 ) )
      | ~ ( v1_tdlat_3 @ X25 )
      | ( v2_tex_2 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X25 ) @ X26 )
      | ~ ( v1_tdlat_3 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) )
           => ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) )
              & ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v1_tdlat_3 @ ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( v2_pre_topc @ ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_tex_2])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('70',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','77'])).

thf('79',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_xboole_0 @ ( k1_connsp_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['9','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aaU60Ej33I
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 18:08:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 103 iterations in 0.083s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.55  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.23/0.55  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.55  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.23/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.55  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.23/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.23/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.55  thf(t36_tex_2, conjecture,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.55           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i]:
% 0.23/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.55            ( l1_pre_topc @ A ) ) =>
% 0.23/0.55          ( ![B:$i]:
% 0.23/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.55              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.23/0.55  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t30_connsp_2, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.56           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.23/0.56  thf('1', plain,
% 0.23/0.56      (![X16 : $i, X17 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.23/0.56          | (r2_hidden @ X16 @ (k1_connsp_2 @ X17 @ X16))
% 0.23/0.56          | ~ (l1_pre_topc @ X17)
% 0.23/0.56          | ~ (v2_pre_topc @ X17)
% 0.23/0.56          | (v2_struct_0 @ X17))),
% 0.23/0.56      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.23/0.56  thf('2', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | (r2_hidden @ sk_B_1 @ (k1_connsp_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.56  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('5', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_A)
% 0.23/0.56        | (r2_hidden @ sk_B_1 @ (k1_connsp_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.23/0.56  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('7', plain, ((r2_hidden @ sk_B_1 @ (k1_connsp_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.56  thf(d1_xboole_0, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.56  thf('8', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.56  thf('9', plain, (~ (v1_xboole_0 @ (k1_connsp_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.56  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(dt_k1_connsp_2, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56       ( m1_subset_1 @
% 0.23/0.56         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.56  thf('11', plain,
% 0.23/0.56      (![X14 : $i, X15 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X14)
% 0.23/0.56          | ~ (v2_pre_topc @ X14)
% 0.23/0.56          | (v2_struct_0 @ X14)
% 0.23/0.56          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.23/0.56          | (m1_subset_1 @ (k1_connsp_2 @ X14 @ X15) @ 
% 0.23/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.23/0.56  thf('12', plain,
% 0.23/0.56      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B_1) @ 
% 0.23/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.56  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('15', plain,
% 0.23/0.56      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B_1) @ 
% 0.23/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.56        | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.23/0.56  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('17', plain,
% 0.23/0.56      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B_1) @ 
% 0.23/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.23/0.56  thf(cc1_subset_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.23/0.56  thf('18', plain,
% 0.23/0.56      (![X6 : $i, X7 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.23/0.56          | (v1_xboole_0 @ X6)
% 0.23/0.56          | ~ (v1_xboole_0 @ X7))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.23/0.56  thf('19', plain,
% 0.23/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v1_xboole_0 @ (k1_connsp_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.56  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(t2_subset, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.56  thf('21', plain,
% 0.23/0.56      (![X8 : $i, X9 : $i]:
% 0.23/0.56         ((r2_hidden @ X8 @ X9)
% 0.23/0.56          | (v1_xboole_0 @ X9)
% 0.23/0.56          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.23/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.56  thf('22', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.56  thf(t63_subset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.23/0.56       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.23/0.56  thf('23', plain,
% 0.23/0.56      (![X4 : $i, X5 : $i]:
% 0.23/0.56         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 0.23/0.56          | ~ (r2_hidden @ X4 @ X5))),
% 0.23/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.23/0.56  thf('24', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.23/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.56  thf('25', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.56  thf('26', plain,
% 0.23/0.56      (![X12 : $i, X13 : $i]:
% 0.23/0.56         ((v1_xboole_0 @ X12)
% 0.23/0.56          | ~ (m1_subset_1 @ X13 @ X12)
% 0.23/0.56          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.23/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.56  thf('27', plain,
% 0.23/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.56  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(dt_k1_tex_2, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.23/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.23/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.23/0.56         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.23/0.56  thf('29', plain,
% 0.23/0.56      (![X21 : $i, X22 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X21)
% 0.23/0.56          | (v2_struct_0 @ X21)
% 0.23/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.23/0.56          | (v1_pre_topc @ (k1_tex_2 @ X21 @ X22)))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.56  thf('30', plain,
% 0.23/0.56      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.56  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('32', plain,
% 0.23/0.56      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.56  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('34', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['32', '33'])).
% 0.23/0.56  thf(d4_tex_2, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.56           ( ![C:$i]:
% 0.23/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.23/0.56                 ( m1_pre_topc @ C @ A ) ) =>
% 0.23/0.56               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.23/0.56                 ( ( u1_struct_0 @ C ) =
% 0.23/0.56                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.23/0.56  thf('35', plain,
% 0.23/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.23/0.56          | ((X20) != (k1_tex_2 @ X19 @ X18))
% 0.23/0.56          | ((u1_struct_0 @ X20) = (k6_domain_1 @ (u1_struct_0 @ X19) @ X18))
% 0.23/0.56          | ~ (m1_pre_topc @ X20 @ X19)
% 0.23/0.56          | ~ (v1_pre_topc @ X20)
% 0.23/0.56          | (v2_struct_0 @ X20)
% 0.23/0.56          | ~ (l1_pre_topc @ X19)
% 0.23/0.56          | (v2_struct_0 @ X19))),
% 0.23/0.56      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.23/0.56  thf('36', plain,
% 0.23/0.56      (![X18 : $i, X19 : $i]:
% 0.23/0.56         ((v2_struct_0 @ X19)
% 0.23/0.56          | ~ (l1_pre_topc @ X19)
% 0.23/0.56          | (v2_struct_0 @ (k1_tex_2 @ X19 @ X18))
% 0.23/0.56          | ~ (v1_pre_topc @ (k1_tex_2 @ X19 @ X18))
% 0.23/0.56          | ~ (m1_pre_topc @ (k1_tex_2 @ X19 @ X18) @ X19)
% 0.23/0.56          | ((u1_struct_0 @ (k1_tex_2 @ X19 @ X18))
% 0.23/0.56              = (k6_domain_1 @ (u1_struct_0 @ X19) @ X18))
% 0.23/0.56          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19)))),
% 0.23/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.23/0.56  thf('37', plain,
% 0.23/0.56      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.23/0.56        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['34', '36'])).
% 0.23/0.56  thf('38', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('39', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('40', plain,
% 0.23/0.56      (![X21 : $i, X22 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X21)
% 0.23/0.56          | (v2_struct_0 @ X21)
% 0.23/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.23/0.56          | (m1_pre_topc @ (k1_tex_2 @ X21 @ X22) @ X21))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.56  thf('41', plain,
% 0.23/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.23/0.56  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('43', plain,
% 0.23/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.23/0.56  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('45', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.23/0.56      inference('clc', [status(thm)], ['43', '44'])).
% 0.23/0.56  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('47', plain,
% 0.23/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['37', '38', '45', '46'])).
% 0.23/0.56  thf('48', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('49', plain,
% 0.23/0.56      (![X21 : $i, X22 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X21)
% 0.23/0.56          | (v2_struct_0 @ X21)
% 0.23/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.23/0.56          | ~ (v2_struct_0 @ (k1_tex_2 @ X21 @ X22)))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.56  thf('50', plain,
% 0.23/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.23/0.56  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('52', plain,
% 0.23/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['50', '51'])).
% 0.23/0.56  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('54', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['52', '53'])).
% 0.23/0.56  thf('55', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_A)
% 0.23/0.56        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.23/0.56      inference('clc', [status(thm)], ['47', '54'])).
% 0.23/0.56  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('57', plain,
% 0.23/0.56      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['55', '56'])).
% 0.23/0.56  thf(t26_tex_2, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.56           ( ![C:$i]:
% 0.23/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.23/0.56                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.23/0.56  thf('58', plain,
% 0.23/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.23/0.56         ((v2_struct_0 @ X25)
% 0.23/0.56          | ~ (m1_pre_topc @ X25 @ X26)
% 0.23/0.56          | ((X27) != (u1_struct_0 @ X25))
% 0.23/0.56          | ~ (v1_tdlat_3 @ X25)
% 0.23/0.56          | (v2_tex_2 @ X27 @ X26)
% 0.23/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.23/0.56          | ~ (l1_pre_topc @ X26)
% 0.23/0.56          | (v2_struct_0 @ X26))),
% 0.23/0.56      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.23/0.56  thf('59', plain,
% 0.23/0.56      (![X25 : $i, X26 : $i]:
% 0.23/0.56         ((v2_struct_0 @ X26)
% 0.23/0.56          | ~ (l1_pre_topc @ X26)
% 0.23/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.23/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.23/0.56          | (v2_tex_2 @ (u1_struct_0 @ X25) @ X26)
% 0.23/0.56          | ~ (v1_tdlat_3 @ X25)
% 0.23/0.56          | ~ (m1_pre_topc @ X25 @ X26)
% 0.23/0.56          | (v2_struct_0 @ X25))),
% 0.23/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.23/0.56  thf('60', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.23/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.56          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.23/0.56          | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | (v2_struct_0 @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['57', '59'])).
% 0.23/0.56  thf('61', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(t24_tex_2, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.56           ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.23/0.56             ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.23/0.56               ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.56  thf('62', plain,
% 0.23/0.56      (![X23 : $i, X24 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.23/0.56          | (v1_tdlat_3 @ (k1_tex_2 @ X24 @ X23))
% 0.23/0.56          | ~ (v2_pre_topc @ (k1_tex_2 @ X24 @ X23))
% 0.23/0.56          | ~ (l1_pre_topc @ X24)
% 0.23/0.56          | (v2_struct_0 @ X24))),
% 0.23/0.56      inference('cnf', [status(esa)], [t24_tex_2])).
% 0.23/0.56  thf('63', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.23/0.56  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('65', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('demod', [status(thm)], ['63', '64'])).
% 0.23/0.56  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('67', plain,
% 0.23/0.56      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.23/0.56  thf('68', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.23/0.56      inference('clc', [status(thm)], ['43', '44'])).
% 0.23/0.56  thf(cc1_pre_topc, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.23/0.56  thf('69', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i]:
% 0.23/0.56         (~ (m1_pre_topc @ X10 @ X11)
% 0.23/0.56          | (v2_pre_topc @ X10)
% 0.23/0.56          | ~ (l1_pre_topc @ X11)
% 0.23/0.56          | ~ (v2_pre_topc @ X11))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.23/0.56  thf('70', plain,
% 0.23/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.23/0.56  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('73', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.23/0.56  thf('74', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['67', '73'])).
% 0.23/0.56  thf('75', plain,
% 0.23/0.56      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['55', '56'])).
% 0.23/0.56  thf('76', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.23/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.56          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.23/0.56          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | (v2_struct_0 @ X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['60', '74', '75'])).
% 0.23/0.56  thf('77', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.23/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56          | (v2_struct_0 @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.23/0.56          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.23/0.56          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['27', '76'])).
% 0.23/0.56  thf('78', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.23/0.56        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['24', '77'])).
% 0.23/0.56  thf('79', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.23/0.56      inference('clc', [status(thm)], ['43', '44'])).
% 0.23/0.56  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('81', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.23/0.56  thf('82', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_A)
% 0.23/0.56        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('simplify', [status(thm)], ['81'])).
% 0.23/0.56  thf('83', plain,
% 0.23/0.56      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('84', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.23/0.56  thf('85', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['52', '53'])).
% 0.23/0.56  thf('86', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('clc', [status(thm)], ['84', '85'])).
% 0.23/0.56  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('88', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('clc', [status(thm)], ['86', '87'])).
% 0.23/0.56  thf('89', plain, ((v1_xboole_0 @ (k1_connsp_2 @ sk_A @ sk_B_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['19', '88'])).
% 0.23/0.56  thf('90', plain, ($false), inference('demod', [status(thm)], ['9', '89'])).
% 0.23/0.56  
% 0.23/0.56  % SZS output end Refutation
% 0.23/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
