%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvbt4gdFC6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 277 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   20
%              Number of atoms          :  953 (3091 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X14 @ ( k1_connsp_2 @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_connsp_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_connsp_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k6_domain_1 @ X10 @ X11 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('28',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

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

thf('33',plain,(
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

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X17 @ X16 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X17 @ X16 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X17 @ X16 ) @ X17 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X17 @ X16 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('39',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('48',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['45','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['53','54'])).

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

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ~ ( v1_tdlat_3 @ X23 )
      | ( v2_tex_2 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X23 ) @ X24 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( v1_tdlat_3 @ ( k1_tex_2 @ X22 @ X21 ) )
      | ~ ( v2_pre_topc @ ( k1_tex_2 @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t24_tex_2])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('68',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','71'])).

thf('73',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','75'])).

thf('77',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','86'])).

thf('88',plain,(
    $false ),
    inference('sup-',[status(thm)],['7','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvbt4gdFC6
% 0.14/0.37  % Computer   : n010.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:25:45 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 66 iterations in 0.043s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.24/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.24/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.24/0.52  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.24/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.52  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.24/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.52  thf(t36_tex_2, conjecture,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i]:
% 0.24/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.52            ( l1_pre_topc @ A ) ) =>
% 0.24/0.52          ( ![B:$i]:
% 0.24/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.24/0.52  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t30_connsp_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.24/0.52          | (r2_hidden @ X14 @ (k1_connsp_2 @ X15 @ X14))
% 0.24/0.52          | ~ (l1_pre_topc @ X15)
% 0.24/0.52          | ~ (v2_pre_topc @ X15)
% 0.24/0.52          | (v2_struct_0 @ X15))),
% 0.24/0.52      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (r2_hidden @ sk_B @ (k1_connsp_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.52  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ (k1_connsp_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.24/0.52  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('7', plain, ((r2_hidden @ sk_B @ (k1_connsp_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(dt_k1_connsp_2, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52       ( m1_subset_1 @
% 0.24/0.52         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X12)
% 0.24/0.52          | ~ (v2_pre_topc @ X12)
% 0.24/0.52          | (v2_struct_0 @ X12)
% 0.24/0.52          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.24/0.52          | (m1_subset_1 @ (k1_connsp_2 @ X12 @ X13) @ 
% 0.24/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.24/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.52  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.24/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.24/0.52  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('15', plain,
% 0.24/0.52      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.24/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf(t5_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.24/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.24/0.52  thf('16', plain,
% 0.24/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.24/0.52          | ~ (v1_xboole_0 @ X7)
% 0.24/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.52  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t2_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.24/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (![X3 : $i, X4 : $i]:
% 0.24/0.52         ((r2_hidden @ X3 @ X4)
% 0.24/0.52          | (v1_xboole_0 @ X4)
% 0.24/0.52          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.24/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.52  thf(t63_subset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.24/0.52       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      (![X1 : $i, X2 : $i]:
% 0.24/0.52         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.24/0.52          | ~ (r2_hidden @ X1 @ X2))),
% 0.24/0.52      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.24/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.52  thf('23', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         ((v1_xboole_0 @ X10)
% 0.24/0.52          | ~ (m1_subset_1 @ X11 @ X10)
% 0.24/0.52          | ((k6_domain_1 @ X10 @ X11) = (k1_tarski @ X11)))),
% 0.24/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.24/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.52  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(dt_k1_tex_2, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.24/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.24/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.24/0.52         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (![X19 : $i, X20 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X19)
% 0.24/0.52          | (v2_struct_0 @ X19)
% 0.24/0.52          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.24/0.52          | (v1_pre_topc @ (k1_tex_2 @ X19 @ X20)))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('28', plain,
% 0.24/0.52      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.24/0.52  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('32', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['30', '31'])).
% 0.24/0.52  thf(d4_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.24/0.52                 ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.52               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.24/0.52                 ( ( u1_struct_0 @ C ) =
% 0.24/0.52                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf('33', plain,
% 0.24/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.24/0.52          | ((X18) != (k1_tex_2 @ X17 @ X16))
% 0.24/0.52          | ((u1_struct_0 @ X18) = (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 0.24/0.52          | ~ (m1_pre_topc @ X18 @ X17)
% 0.24/0.52          | ~ (v1_pre_topc @ X18)
% 0.24/0.52          | (v2_struct_0 @ X18)
% 0.24/0.52          | ~ (l1_pre_topc @ X17)
% 0.24/0.52          | (v2_struct_0 @ X17))),
% 0.24/0.52      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      (![X16 : $i, X17 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X17)
% 0.24/0.52          | ~ (l1_pre_topc @ X17)
% 0.24/0.52          | (v2_struct_0 @ (k1_tex_2 @ X17 @ X16))
% 0.24/0.52          | ~ (v1_pre_topc @ (k1_tex_2 @ X17 @ X16))
% 0.24/0.52          | ~ (m1_pre_topc @ (k1_tex_2 @ X17 @ X16) @ X17)
% 0.24/0.52          | ((u1_struct_0 @ (k1_tex_2 @ X17 @ X16))
% 0.24/0.52              = (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 0.24/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.24/0.52        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['32', '34'])).
% 0.24/0.52  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('38', plain,
% 0.24/0.52      (![X19 : $i, X20 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X19)
% 0.24/0.52          | (v2_struct_0 @ X19)
% 0.24/0.52          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.24/0.52          | (m1_pre_topc @ (k1_tex_2 @ X19 @ X20) @ X19))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.24/0.52  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('41', plain,
% 0.24/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.24/0.52  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('43', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['41', '42'])).
% 0.24/0.52  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('45', plain,
% 0.24/0.52      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['35', '36', '43', '44'])).
% 0.24/0.52  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('47', plain,
% 0.24/0.52      (![X19 : $i, X20 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X19)
% 0.24/0.52          | (v2_struct_0 @ X19)
% 0.24/0.52          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.24/0.52          | ~ (v2_struct_0 @ (k1_tex_2 @ X19 @ X20)))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('48', plain,
% 0.24/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.24/0.52  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('50', plain,
% 0.24/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.24/0.52  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('52', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['50', '51'])).
% 0.24/0.52  thf('53', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.24/0.52      inference('clc', [status(thm)], ['45', '52'])).
% 0.24/0.52  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('55', plain,
% 0.24/0.52      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.24/0.52  thf(t26_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.24/0.52                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf('56', plain,
% 0.24/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X23)
% 0.24/0.52          | ~ (m1_pre_topc @ X23 @ X24)
% 0.24/0.52          | ((X25) != (u1_struct_0 @ X23))
% 0.24/0.52          | ~ (v1_tdlat_3 @ X23)
% 0.24/0.52          | (v2_tex_2 @ X25 @ X24)
% 0.24/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.24/0.52          | ~ (l1_pre_topc @ X24)
% 0.24/0.52          | (v2_struct_0 @ X24))),
% 0.24/0.52      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.24/0.52  thf('57', plain,
% 0.24/0.52      (![X23 : $i, X24 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X24)
% 0.24/0.52          | ~ (l1_pre_topc @ X24)
% 0.24/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.24/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.24/0.52          | (v2_tex_2 @ (u1_struct_0 @ X23) @ X24)
% 0.24/0.52          | ~ (v1_tdlat_3 @ X23)
% 0.24/0.52          | ~ (m1_pre_topc @ X23 @ X24)
% 0.24/0.52          | (v2_struct_0 @ X23))),
% 0.24/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.24/0.52  thf('58', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.24/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.24/0.52          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.24/0.52          | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0)
% 0.24/0.52          | ~ (l1_pre_topc @ X0)
% 0.24/0.52          | (v2_struct_0 @ X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['55', '57'])).
% 0.24/0.52  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t24_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.24/0.52             ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.24/0.52               ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.52  thf('60', plain,
% 0.24/0.52      (![X21 : $i, X22 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.24/0.52          | (v1_tdlat_3 @ (k1_tex_2 @ X22 @ X21))
% 0.24/0.52          | ~ (v2_pre_topc @ (k1_tex_2 @ X22 @ X21))
% 0.24/0.52          | ~ (l1_pre_topc @ X22)
% 0.24/0.52          | (v2_struct_0 @ X22))),
% 0.24/0.52      inference('cnf', [status(esa)], [t24_tex_2])).
% 0.24/0.52  thf('61', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.24/0.52  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('63', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.24/0.52  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('65', plain,
% 0.24/0.52      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('clc', [status(thm)], ['63', '64'])).
% 0.24/0.52  thf('66', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['41', '42'])).
% 0.24/0.52  thf(cc1_pre_topc, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.24/0.52  thf('67', plain,
% 0.24/0.52      (![X8 : $i, X9 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X8 @ X9)
% 0.24/0.52          | (v2_pre_topc @ X8)
% 0.24/0.52          | ~ (l1_pre_topc @ X9)
% 0.24/0.52          | ~ (v2_pre_topc @ X9))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.24/0.52  thf('68', plain,
% 0.24/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.24/0.52  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('71', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.24/0.52  thf('72', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['65', '71'])).
% 0.24/0.52  thf('73', plain,
% 0.24/0.52      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.24/0.52  thf('74', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.24/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.24/0.52          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.24/0.52          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.24/0.52          | ~ (l1_pre_topc @ X0)
% 0.24/0.52          | (v2_struct_0 @ X0))),
% 0.24/0.52      inference('demod', [status(thm)], ['58', '72', '73'])).
% 0.24/0.52  thf('75', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.24/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.24/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52          | (v2_struct_0 @ X0)
% 0.24/0.52          | ~ (l1_pre_topc @ X0)
% 0.24/0.52          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.24/0.52          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.24/0.52          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['25', '74'])).
% 0.24/0.52  thf('76', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['22', '75'])).
% 0.24/0.52  thf('77', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['41', '42'])).
% 0.24/0.52  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('79', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.24/0.52  thf('80', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['79'])).
% 0.24/0.52  thf('81', plain,
% 0.24/0.52      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('82', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.24/0.52  thf('83', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['50', '51'])).
% 0.24/0.52  thf('84', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['82', '83'])).
% 0.24/0.52  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('86', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('clc', [status(thm)], ['84', '85'])).
% 0.24/0.52  thf('87', plain,
% 0.24/0.52      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['17', '86'])).
% 0.24/0.52  thf('88', plain, ($false), inference('sup-', [status(thm)], ['7', '87'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
