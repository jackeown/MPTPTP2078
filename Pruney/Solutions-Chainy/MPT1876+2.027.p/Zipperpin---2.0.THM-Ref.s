%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QIleLmImap

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 824 expanded)
%              Number of leaves         :   34 ( 234 expanded)
%              Depth                    :   25
%              Number of atoms          :  958 (9397 expanded)
%              Number of equality atoms :   17 ( 100 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t44_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ~ ( v2_struct_0 @ ( sk_C @ X17 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i] :
      ( ~ ( v1_zfmisc_1 @ X15 )
      | ( X15
        = ( k6_domain_1 @ X15 @ ( sk_B @ X15 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('11',plain,(
    ! [X15: $i] :
      ( ~ ( v1_zfmisc_1 @ X15 )
      | ( m1_subset_1 @ ( sk_B @ X15 ) @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('18',plain,(
    ! [X15: $i] :
      ( ~ ( v1_zfmisc_1 @ X15 )
      | ( m1_subset_1 @ ( sk_B @ X15 ) @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('35',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','40'])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31','32','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['16','44'])).

thf('46',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('47',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('51',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('53',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','51','52'])).

thf('54',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( m1_pre_topc @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','53'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf(cc31_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B ) ) ) ) ) )).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v7_struct_0 @ X13 )
      | ~ ( v1_tdlat_3 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_tdlat_3 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc31_tex_2])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( v1_tdlat_3 @ ( sk_C @ X17 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','53'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( X17
        = ( u1_struct_0 @ ( sk_C @ X17 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','53'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('101',plain,(
    ! [X10: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ~ ( v7_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('102',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('104',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','51'])).

thf('105',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','105'])).

thf('107',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('112',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('113',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','113'])).

thf('115',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['89','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['59','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QIleLmImap
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 78 iterations in 0.047s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.19/0.47  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.19/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.19/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.47  thf(t44_tex_2, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.19/0.47         ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.47           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.47            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.47                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.47              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t34_tex_2, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.47           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.19/0.47                ( ![C:$i]:
% 0.19/0.47                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.19/0.47                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.47                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X17)
% 0.19/0.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.47          | ~ (v2_tex_2 @ X17 @ X18)
% 0.19/0.47          | ~ (v2_struct_0 @ (sk_C @ X17 @ X18))
% 0.19/0.47          | ~ (l1_pre_topc @ X18)
% 0.19/0.47          | ~ (v2_pre_topc @ X18)
% 0.19/0.47          | (v2_struct_0 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.47        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.47        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.47      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.19/0.47  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['6'])).
% 0.19/0.47  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.47      inference('split', [status(esa)], ['8'])).
% 0.19/0.47  thf(d1_tex_2, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47       ( ( v1_zfmisc_1 @ A ) <=>
% 0.19/0.47         ( ?[B:$i]:
% 0.19/0.47           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X15 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X15)
% 0.19/0.47          | ((X15) = (k6_domain_1 @ X15 @ (sk_B @ X15)))
% 0.19/0.47          | (v1_xboole_0 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X15 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X15)
% 0.19/0.47          | (m1_subset_1 @ (sk_B @ X15) @ X15)
% 0.19/0.47          | (v1_xboole_0 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.19/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X11 : $i, X12 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X11)
% 0.19/0.47          | ~ (m1_subset_1 @ X12 @ X11)
% 0.19/0.47          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['10', '14'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.19/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.47  thf('17', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('split', [status(esa)], ['6'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X15 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X15)
% 0.19/0.47          | (m1_subset_1 @ (sk_B @ X15) @ X15)
% 0.19/0.47          | (v1_xboole_0 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.19/0.47  thf(t2_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i]:
% 0.19/0.47         ((r2_hidden @ X2 @ X3)
% 0.19/0.47          | (v1_xboole_0 @ X3)
% 0.19/0.47          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_B @ X0) @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t4_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.19/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X4 @ X5)
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.19/0.47          | (m1_subset_1 @ X4 @ X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.47        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.19/0.47        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['21', '24'])).
% 0.19/0.47  thf('26', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('27', plain,
% 0.19/0.47      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.19/0.47        | ~ (v1_zfmisc_1 @ sk_B_1))),
% 0.19/0.47      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))
% 0.19/0.47         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['17', '27'])).
% 0.19/0.47  thf(t36_tex_2, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (![X19 : $i, X20 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.19/0.47          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.19/0.47          | ~ (l1_pre_topc @ X20)
% 0.19/0.47          | ~ (v2_pre_topc @ X20)
% 0.19/0.47          | (v2_struct_0 @ X20))),
% 0.19/0.47      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      ((((v2_struct_0 @ sk_A)
% 0.19/0.47         | ~ (v2_pre_topc @ sk_A)
% 0.19/0.47         | ~ (l1_pre_topc @ sk_A)
% 0.19/0.47         | (v2_tex_2 @ 
% 0.19/0.47            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)))
% 0.19/0.47         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.47  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))
% 0.19/0.47         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['17', '27'])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      (![X11 : $i, X12 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X11)
% 0.19/0.47          | ~ (m1_subset_1 @ X12 @ X11)
% 0.19/0.47          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.19/0.47           = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.19/0.47         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.47  thf('36', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc1_subset_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.47  thf('38', plain,
% 0.19/0.47      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.47  thf('39', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('40', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('clc', [status(thm)], ['38', '39'])).
% 0.19/0.47  thf('41', plain,
% 0.19/0.47      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.19/0.47          = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.19/0.47         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('clc', [status(thm)], ['35', '40'])).
% 0.19/0.47  thf('42', plain,
% 0.19/0.47      ((((v2_struct_0 @ sk_A)
% 0.19/0.47         | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)))
% 0.19/0.47         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('demod', [status(thm)], ['30', '31', '32', '41'])).
% 0.19/0.47  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('44', plain,
% 0.19/0.47      (((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))
% 0.19/0.47         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('clc', [status(thm)], ['42', '43'])).
% 0.19/0.47  thf('45', plain,
% 0.19/0.47      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.47         | (v1_xboole_0 @ sk_B_1)
% 0.19/0.47         | ~ (v1_zfmisc_1 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['16', '44'])).
% 0.19/0.47  thf('46', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('split', [status(esa)], ['6'])).
% 0.19/0.47  thf('47', plain,
% 0.19/0.47      ((((v2_tex_2 @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.19/0.47         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.47  thf('48', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('49', plain,
% 0.19/0.47      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.47      inference('clc', [status(thm)], ['47', '48'])).
% 0.19/0.47  thf('50', plain,
% 0.19/0.47      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['8'])).
% 0.19/0.47  thf('51', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.47  thf('52', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.19/0.47      inference('split', [status(esa)], ['6'])).
% 0.19/0.47  thf('53', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['9', '51', '52'])).
% 0.19/0.47  thf('54', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['7', '53'])).
% 0.19/0.47  thf('55', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '54'])).
% 0.19/0.47  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('57', plain,
% 0.19/0.47      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.47      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.47  thf('58', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('59', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.19/0.47      inference('clc', [status(thm)], ['57', '58'])).
% 0.19/0.47  thf('60', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('61', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X17)
% 0.19/0.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.47          | ~ (v2_tex_2 @ X17 @ X18)
% 0.19/0.47          | (m1_pre_topc @ (sk_C @ X17 @ X18) @ X18)
% 0.19/0.47          | ~ (l1_pre_topc @ X18)
% 0.19/0.47          | ~ (v2_pre_topc @ X18)
% 0.19/0.47          | (v2_struct_0 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.47  thf('62', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.19/0.47        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.47  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('65', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['7', '53'])).
% 0.19/0.47  thf('66', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.19/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.47      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.19/0.47  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('68', plain,
% 0.19/0.47      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.19/0.47      inference('clc', [status(thm)], ['66', '67'])).
% 0.19/0.47  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('70', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.19/0.47      inference('clc', [status(thm)], ['68', '69'])).
% 0.19/0.47  thf(cc31_tex_2, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.19/0.47         ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.47           ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) ) =>
% 0.19/0.47             ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('71', plain,
% 0.19/0.47      (![X13 : $i, X14 : $i]:
% 0.19/0.47         (~ (m1_pre_topc @ X13 @ X14)
% 0.19/0.47          | (v7_struct_0 @ X13)
% 0.19/0.47          | ~ (v1_tdlat_3 @ X13)
% 0.19/0.47          | (v2_struct_0 @ X13)
% 0.19/0.47          | ~ (l1_pre_topc @ X14)
% 0.19/0.47          | ~ (v2_tdlat_3 @ X14)
% 0.19/0.47          | ~ (v2_pre_topc @ X14)
% 0.19/0.47          | (v2_struct_0 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc31_tex_2])).
% 0.19/0.47  thf('72', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48        | ~ (v2_tdlat_3 @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.48  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('74', plain, ((v2_tdlat_3 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('76', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('77', plain,
% 0.19/0.48      (![X17 : $i, X18 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X17)
% 0.19/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.48          | ~ (v2_tex_2 @ X17 @ X18)
% 0.19/0.48          | (v1_tdlat_3 @ (sk_C @ X17 @ X18))
% 0.19/0.48          | ~ (l1_pre_topc @ X18)
% 0.19/0.48          | ~ (v2_pre_topc @ X18)
% 0.19/0.48          | (v2_struct_0 @ X18))),
% 0.19/0.48      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.48  thf('78', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['76', '77'])).
% 0.19/0.48  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('81', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['7', '53'])).
% 0.19/0.48  thf('82', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.19/0.48  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('84', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B_1) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('clc', [status(thm)], ['82', '83'])).
% 0.19/0.48  thf('85', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('86', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.19/0.48      inference('clc', [status(thm)], ['84', '85'])).
% 0.19/0.48  thf('87', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['72', '73', '74', '75', '86'])).
% 0.19/0.48  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('89', plain,
% 0.19/0.48      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('clc', [status(thm)], ['87', '88'])).
% 0.19/0.48  thf('90', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('91', plain,
% 0.19/0.48      (![X17 : $i, X18 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X17)
% 0.19/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.48          | ~ (v2_tex_2 @ X17 @ X18)
% 0.19/0.48          | ((X17) = (u1_struct_0 @ (sk_C @ X17 @ X18)))
% 0.19/0.48          | ~ (l1_pre_topc @ X18)
% 0.19/0.48          | ~ (v2_pre_topc @ X18)
% 0.19/0.48          | (v2_struct_0 @ X18))),
% 0.19/0.48      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.48  thf('92', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.19/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['90', '91'])).
% 0.19/0.48  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('95', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['7', '53'])).
% 0.19/0.48  thf('96', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.19/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.19/0.48  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('98', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.48        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.19/0.48      inference('clc', [status(thm)], ['96', '97'])).
% 0.19/0.48  thf('99', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('100', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('clc', [status(thm)], ['98', '99'])).
% 0.19/0.48  thf(fc7_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.19/0.48  thf('101', plain,
% 0.19/0.48      (![X10 : $i]:
% 0.19/0.48         ((v1_zfmisc_1 @ (u1_struct_0 @ X10))
% 0.19/0.48          | ~ (l1_struct_0 @ X10)
% 0.19/0.48          | ~ (v7_struct_0 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.19/0.48  thf('102', plain,
% 0.19/0.48      (((v1_zfmisc_1 @ sk_B_1)
% 0.19/0.48        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['100', '101'])).
% 0.19/0.48  thf('103', plain,
% 0.19/0.48      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.48      inference('split', [status(esa)], ['8'])).
% 0.19/0.48  thf('104', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['9', '51'])).
% 0.19/0.48  thf('105', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['103', '104'])).
% 0.19/0.48  thf('106', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.48        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('clc', [status(thm)], ['102', '105'])).
% 0.19/0.48  thf('107', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['68', '69'])).
% 0.19/0.48  thf(dt_m1_pre_topc, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.48  thf('108', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]:
% 0.19/0.48         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.48  thf('109', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['107', '108'])).
% 0.19/0.48  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('111', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['109', '110'])).
% 0.19/0.48  thf(dt_l1_pre_topc, axiom,
% 0.19/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.48  thf('112', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('113', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['111', '112'])).
% 0.19/0.48  thf('114', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['106', '113'])).
% 0.19/0.48  thf('115', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.19/0.48      inference('clc', [status(thm)], ['89', '114'])).
% 0.19/0.48  thf('116', plain, ($false), inference('demod', [status(thm)], ['59', '115'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
