%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cyqAqWkKRG

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:40 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 769 expanded)
%              Number of leaves         :   32 ( 218 expanded)
%              Depth                    :   36
%              Number of atoms          : 1615 (10182 expanded)
%              Number of equality atoms :   39 ( 237 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_pre_topc @ ( sk_C_1 @ X23 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X23 @ X24 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( X23
        = ( u1_struct_0 @ ( sk_C_1 @ X23 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( u1_struct_0 @ X22 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) )
      | ( X22
        = ( k1_tex_2 @ X21 @ X20 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( v1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( X0
        = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( X0
        = ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_B_1 )
     != ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) @ sk_A )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X23 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('47',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('50',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( v1_tdlat_3 @ ( k1_tex_2 @ X26 @ X25 ) )
      | ~ ( v2_pre_topc @ ( k1_tex_2 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t24_tex_2])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

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

thf('68',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( X29
       != ( u1_struct_0 @ X27 ) )
      | ~ ( v1_tdlat_3 @ X27 )
      | ( v2_tex_2 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X27 ) @ X28 )
      | ~ ( v1_tdlat_3 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['44','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('83',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('88',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( v2_tex_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('94',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('95',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['93','97'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('99',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
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
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cyqAqWkKRG
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.63/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.82  % Solved by: fo/fo7.sh
% 0.63/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.82  % done 554 iterations in 0.359s
% 0.63/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.82  % SZS output start Refutation
% 0.63/0.82  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.63/0.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.63/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.63/0.82  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.63/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.82  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.63/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.63/0.82  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.63/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.63/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.63/0.82  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.63/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.82  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.63/0.82  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.63/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.63/0.82  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.63/0.82  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.63/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.63/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.82  thf(t36_tex_2, conjecture,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.63/0.82           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.63/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.82    (~( ![A:$i]:
% 0.63/0.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.63/0.82            ( l1_pre_topc @ A ) ) =>
% 0.63/0.82          ( ![B:$i]:
% 0.63/0.82            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.63/0.82              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.63/0.82    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.63/0.82  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(redefinition_k6_domain_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.63/0.82       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.63/0.82  thf('2', plain,
% 0.63/0.82      (![X18 : $i, X19 : $i]:
% 0.63/0.82         ((v1_xboole_0 @ X18)
% 0.63/0.82          | ~ (m1_subset_1 @ X19 @ X18)
% 0.63/0.82          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.63/0.82  thf('3', plain,
% 0.63/0.82      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.63/0.82  thf('4', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(dt_k6_domain_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.63/0.82       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.63/0.82  thf('5', plain,
% 0.63/0.82      (![X16 : $i, X17 : $i]:
% 0.63/0.82         ((v1_xboole_0 @ X16)
% 0.63/0.82          | ~ (m1_subset_1 @ X17 @ X16)
% 0.63/0.82          | (m1_subset_1 @ (k6_domain_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.63/0.82      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.63/0.82  thf('6', plain,
% 0.63/0.82      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.63/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.63/0.82  thf('7', plain,
% 0.63/0.82      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['3', '6'])).
% 0.63/0.82  thf('8', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['7'])).
% 0.63/0.82  thf(t10_tsep_1, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.63/0.82             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.82           ( ?[C:$i]:
% 0.63/0.82             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.63/0.82               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.63/0.82  thf('9', plain,
% 0.63/0.82      (![X23 : $i, X24 : $i]:
% 0.63/0.82         ((v1_xboole_0 @ X23)
% 0.63/0.82          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.63/0.82          | (v1_pre_topc @ (sk_C_1 @ X23 @ X24))
% 0.63/0.82          | ~ (l1_pre_topc @ X24)
% 0.63/0.82          | (v2_struct_0 @ X24))),
% 0.63/0.82      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.63/0.82  thf('10', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['8', '9'])).
% 0.63/0.82  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('12', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['10', '11'])).
% 0.63/0.82  thf('13', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['7'])).
% 0.63/0.82  thf('14', plain,
% 0.63/0.82      (![X23 : $i, X24 : $i]:
% 0.63/0.82         ((v1_xboole_0 @ X23)
% 0.63/0.82          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.63/0.82          | (m1_pre_topc @ (sk_C_1 @ X23 @ X24) @ X24)
% 0.63/0.82          | ~ (l1_pre_topc @ X24)
% 0.63/0.82          | (v2_struct_0 @ X24))),
% 0.63/0.82      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.63/0.82  thf('15', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.63/0.82  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('17', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['15', '16'])).
% 0.63/0.82  thf('18', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['7'])).
% 0.63/0.82  thf('19', plain,
% 0.63/0.82      (![X23 : $i, X24 : $i]:
% 0.63/0.82         ((v1_xboole_0 @ X23)
% 0.63/0.82          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.63/0.82          | ((X23) = (u1_struct_0 @ (sk_C_1 @ X23 @ X24)))
% 0.63/0.82          | ~ (l1_pre_topc @ X24)
% 0.63/0.82          | (v2_struct_0 @ X24))),
% 0.63/0.82      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.63/0.82  thf('20', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | ((k1_tarski @ sk_B_1)
% 0.63/0.82            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A)))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['18', '19'])).
% 0.63/0.82  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('22', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ((k1_tarski @ sk_B_1)
% 0.63/0.82            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A)))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['20', '21'])).
% 0.63/0.82  thf('23', plain,
% 0.63/0.82      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.63/0.82  thf(d4_tex_2, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.63/0.82           ( ![C:$i]:
% 0.63/0.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.63/0.82                 ( m1_pre_topc @ C @ A ) ) =>
% 0.63/0.82               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.63/0.82                 ( ( u1_struct_0 @ C ) =
% 0.63/0.82                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.63/0.82  thf('24', plain,
% 0.63/0.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.63/0.82          | ((u1_struct_0 @ X22) != (k6_domain_1 @ (u1_struct_0 @ X21) @ X20))
% 0.63/0.82          | ((X22) = (k1_tex_2 @ X21 @ X20))
% 0.63/0.82          | ~ (m1_pre_topc @ X22 @ X21)
% 0.63/0.82          | ~ (v1_pre_topc @ X22)
% 0.63/0.82          | (v2_struct_0 @ X22)
% 0.63/0.82          | ~ (l1_pre_topc @ X21)
% 0.63/0.82          | (v2_struct_0 @ X21))),
% 0.63/0.82      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.63/0.82  thf('25', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((u1_struct_0 @ X0) != (k1_tarski @ sk_B_1))
% 0.63/0.82          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82          | (v2_struct_0 @ sk_A)
% 0.63/0.82          | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82          | (v2_struct_0 @ X0)
% 0.63/0.82          | ~ (v1_pre_topc @ X0)
% 0.63/0.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.82          | ((X0) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.63/0.82  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('28', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((u1_struct_0 @ X0) != (k1_tarski @ sk_B_1))
% 0.63/0.82          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82          | (v2_struct_0 @ sk_A)
% 0.63/0.82          | (v2_struct_0 @ X0)
% 0.63/0.82          | ~ (v1_pre_topc @ X0)
% 0.63/0.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.82          | ((X0) = (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.63/0.82  thf('29', plain,
% 0.63/0.82      ((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | ((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | ~ (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) @ sk_A)
% 0.63/0.82        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['22', '28'])).
% 0.63/0.82  thf('30', plain,
% 0.63/0.82      (((v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | ~ (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) @ sk_A)
% 0.63/0.82        | ((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['29'])).
% 0.63/0.82  thf('31', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | ((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['17', '30'])).
% 0.63/0.82  thf('32', plain,
% 0.63/0.82      (((v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | ((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['31'])).
% 0.63/0.82  thf('33', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | ((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['12', '32'])).
% 0.63/0.82  thf('34', plain,
% 0.63/0.82      (((v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | ((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['33'])).
% 0.63/0.82  thf('35', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['7'])).
% 0.63/0.82  thf('36', plain,
% 0.63/0.82      (![X23 : $i, X24 : $i]:
% 0.63/0.82         ((v1_xboole_0 @ X23)
% 0.63/0.82          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.63/0.82          | ~ (v2_struct_0 @ (sk_C_1 @ X23 @ X24))
% 0.63/0.82          | ~ (l1_pre_topc @ X24)
% 0.63/0.82          | (v2_struct_0 @ X24))),
% 0.63/0.82      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.63/0.82  thf('37', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['35', '36'])).
% 0.63/0.82  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('39', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['37', '38'])).
% 0.63/0.82  thf('40', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | ((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['34', '39'])).
% 0.63/0.82  thf('41', plain,
% 0.63/0.82      ((((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['40'])).
% 0.63/0.82  thf('42', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ((k1_tarski @ sk_B_1)
% 0.63/0.82            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A)))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['20', '21'])).
% 0.63/0.82  thf('43', plain,
% 0.63/0.82      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['41', '42'])).
% 0.63/0.82  thf('44', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['43'])).
% 0.63/0.82  thf('45', plain,
% 0.63/0.82      ((((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['40'])).
% 0.63/0.82  thf('46', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['15', '16'])).
% 0.63/0.82  thf('47', plain,
% 0.63/0.82      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['45', '46'])).
% 0.63/0.82  thf('48', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.63/0.82      inference('simplify', [status(thm)], ['47'])).
% 0.63/0.82  thf('49', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['7'])).
% 0.63/0.82  thf('50', plain,
% 0.63/0.82      ((((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['40'])).
% 0.63/0.82  thf('51', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['15', '16'])).
% 0.63/0.82  thf(cc1_pre_topc, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.63/0.82  thf('52', plain,
% 0.63/0.82      (![X12 : $i, X13 : $i]:
% 0.63/0.82         (~ (m1_pre_topc @ X12 @ X13)
% 0.63/0.82          | (v2_pre_topc @ X12)
% 0.63/0.82          | ~ (l1_pre_topc @ X13)
% 0.63/0.82          | ~ (v2_pre_topc @ X13))),
% 0.63/0.82      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.63/0.82  thf('53', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | ~ (v2_pre_topc @ sk_A)
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['51', '52'])).
% 0.63/0.82  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('56', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A)))),
% 0.63/0.82      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.63/0.82  thf('57', plain,
% 0.63/0.82      (((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['50', '56'])).
% 0.63/0.82  thf('58', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['57'])).
% 0.63/0.82  thf('59', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(t24_tex_2, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.63/0.82           ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.63/0.82             ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.63/0.82               ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ))).
% 0.63/0.82  thf('60', plain,
% 0.63/0.82      (![X25 : $i, X26 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.63/0.82          | (v1_tdlat_3 @ (k1_tex_2 @ X26 @ X25))
% 0.63/0.82          | ~ (v2_pre_topc @ (k1_tex_2 @ X26 @ X25))
% 0.63/0.82          | ~ (l1_pre_topc @ X26)
% 0.63/0.82          | (v2_struct_0 @ X26))),
% 0.63/0.82      inference('cnf', [status(esa)], [t24_tex_2])).
% 0.63/0.82  thf('61', plain,
% 0.63/0.82      (((v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['59', '60'])).
% 0.63/0.82  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('63', plain,
% 0.63/0.82      (((v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['61', '62'])).
% 0.63/0.82  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('65', plain,
% 0.63/0.82      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('clc', [status(thm)], ['63', '64'])).
% 0.63/0.82  thf('66', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['58', '65'])).
% 0.63/0.82  thf('67', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['43'])).
% 0.63/0.82  thf(t26_tex_2, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.63/0.82           ( ![C:$i]:
% 0.63/0.82             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.82               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.63/0.82                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.63/0.82  thf('68', plain,
% 0.63/0.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.63/0.82         ((v2_struct_0 @ X27)
% 0.63/0.82          | ~ (m1_pre_topc @ X27 @ X28)
% 0.63/0.82          | ((X29) != (u1_struct_0 @ X27))
% 0.63/0.82          | ~ (v1_tdlat_3 @ X27)
% 0.63/0.82          | (v2_tex_2 @ X29 @ X28)
% 0.63/0.82          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.82          | ~ (l1_pre_topc @ X28)
% 0.63/0.82          | (v2_struct_0 @ X28))),
% 0.63/0.82      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.63/0.82  thf('69', plain,
% 0.63/0.82      (![X27 : $i, X28 : $i]:
% 0.63/0.82         ((v2_struct_0 @ X28)
% 0.63/0.82          | ~ (l1_pre_topc @ X28)
% 0.63/0.82          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.63/0.82               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.82          | (v2_tex_2 @ (u1_struct_0 @ X27) @ X28)
% 0.63/0.82          | ~ (v1_tdlat_3 @ X27)
% 0.63/0.82          | ~ (m1_pre_topc @ X27 @ X28)
% 0.63/0.82          | (v2_struct_0 @ X27))),
% 0.63/0.82      inference('simplify', [status(thm)], ['68'])).
% 0.63/0.82  thf('70', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.63/0.82          | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82          | (v2_struct_0 @ sk_A)
% 0.63/0.82          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.63/0.82          | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ X0)
% 0.63/0.82          | ~ (l1_pre_topc @ X0)
% 0.63/0.82          | (v2_struct_0 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['67', '69'])).
% 0.63/0.82  thf('71', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82          | (v2_struct_0 @ sk_A)
% 0.63/0.82          | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82          | (v2_struct_0 @ X0)
% 0.63/0.82          | ~ (l1_pre_topc @ X0)
% 0.63/0.82          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ X0)
% 0.63/0.82          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.63/0.82          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82          | (v2_struct_0 @ sk_A)
% 0.63/0.82          | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82          | ~ (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['66', '70'])).
% 0.63/0.82  thf('72', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.63/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.63/0.82          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.63/0.82          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ X0)
% 0.63/0.82          | ~ (l1_pre_topc @ X0)
% 0.63/0.82          | (v2_struct_0 @ X0)
% 0.63/0.82          | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82          | (v2_struct_0 @ sk_A)
% 0.63/0.82          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['71'])).
% 0.63/0.82  thf('73', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ sk_A)
% 0.63/0.82        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.63/0.82        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['49', '72'])).
% 0.63/0.82  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('75', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ sk_A)
% 0.63/0.82        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.63/0.82        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['73', '74'])).
% 0.63/0.82  thf('76', plain,
% 0.63/0.82      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.63/0.82        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['75'])).
% 0.63/0.82  thf('77', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ sk_A)
% 0.63/0.82        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['48', '76'])).
% 0.63/0.82  thf('78', plain,
% 0.63/0.82      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['77'])).
% 0.63/0.82  thf('79', plain,
% 0.63/0.82      (((v2_tex_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['44', '78'])).
% 0.63/0.82  thf('80', plain,
% 0.63/0.82      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_tex_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.63/0.82      inference('simplify', [status(thm)], ['79'])).
% 0.63/0.82  thf('81', plain,
% 0.63/0.82      ((((sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['40'])).
% 0.63/0.82  thf('82', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('demod', [status(thm)], ['37', '38'])).
% 0.63/0.82  thf('83', plain,
% 0.63/0.82      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['81', '82'])).
% 0.63/0.82  thf('84', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | ~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['83'])).
% 0.63/0.82  thf('85', plain,
% 0.63/0.82      (((v2_tex_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['80', '84'])).
% 0.63/0.82  thf('86', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_tex_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.63/0.82      inference('simplify', [status(thm)], ['85'])).
% 0.63/0.82  thf('87', plain,
% 0.63/0.82      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.63/0.82  thf('88', plain,
% 0.63/0.82      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('89', plain,
% 0.63/0.82      ((~ (v2_tex_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['87', '88'])).
% 0.63/0.82  thf('90', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['86', '89'])).
% 0.63/0.82  thf('91', plain,
% 0.63/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.63/0.82        | (v2_struct_0 @ sk_A)
% 0.63/0.82        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['90'])).
% 0.63/0.82  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('93', plain,
% 0.63/0.82      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.63/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('clc', [status(thm)], ['91', '92'])).
% 0.63/0.82  thf(d1_tarski, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.63/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.63/0.82  thf('94', plain,
% 0.63/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.63/0.82         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.63/0.82      inference('cnf', [status(esa)], [d1_tarski])).
% 0.63/0.82  thf('95', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.63/0.82      inference('simplify', [status(thm)], ['94'])).
% 0.63/0.82  thf(d1_xboole_0, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.63/0.82  thf('96', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.63/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.63/0.82  thf('97', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['95', '96'])).
% 0.63/0.82  thf('98', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.63/0.82      inference('clc', [status(thm)], ['93', '97'])).
% 0.63/0.82  thf(fc2_struct_0, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.63/0.82       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.63/0.82  thf('99', plain,
% 0.63/0.82      (![X15 : $i]:
% 0.63/0.82         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.63/0.82          | ~ (l1_struct_0 @ X15)
% 0.63/0.82          | (v2_struct_0 @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.63/0.82  thf('100', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.63/0.82      inference('sup-', [status(thm)], ['98', '99'])).
% 0.63/0.82  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(dt_l1_pre_topc, axiom,
% 0.63/0.82    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.63/0.82  thf('102', plain,
% 0.63/0.82      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.63/0.82      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.63/0.82  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.82      inference('sup-', [status(thm)], ['101', '102'])).
% 0.63/0.82  thf('104', plain, ((v2_struct_0 @ sk_A)),
% 0.63/0.82      inference('demod', [status(thm)], ['100', '103'])).
% 0.63/0.82  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 0.63/0.82  
% 0.63/0.82  % SZS output end Refutation
% 0.63/0.82  
% 0.63/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
