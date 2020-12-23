%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cwm3gSUha8

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 729 expanded)
%              Number of leaves         :   37 ( 217 expanded)
%              Depth                    :   24
%              Number of atoms          :  901 (7999 expanded)
%              Number of equality atoms :   15 (  64 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ~ ( v2_struct_0 @ ( sk_C @ X26 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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

thf('10',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( X25 = X24 )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('32',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['32','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','44'])).

thf('46',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('49',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','47','48'])).

thf('50',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( m1_pre_topc @ ( sk_C @ X26 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','49'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['64','65'])).

thf(cc32_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_tdlat_3 @ X22 )
      | ( v7_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( v1_tdlat_3 @ ( sk_C @ X26 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','49'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( X26
        = ( u1_struct_0 @ ( sk_C @ X26 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','49'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('97',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( v7_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('98',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('100',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','47'])).

thf('101',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['98','101'])).

thf('103',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['64','65'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('108',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','109'])).

thf('111',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['85','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['55','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cwm3gSUha8
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:13:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 100 iterations in 0.058s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.22/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.53  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.22/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.53  thf(t44_tex_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.22/0.53         ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.53            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.53                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t34_tex_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.53                ( ![C:$i]:
% 0.22/0.53                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.22/0.53                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.53                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X26)
% 0.22/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.53          | ~ (v2_tex_2 @ X26 @ X27)
% 0.22/0.53          | ~ (v2_struct_0 @ (sk_C @ X26 @ X27))
% 0.22/0.53          | ~ (l1_pre_topc @ X27)
% 0.22/0.53          | ~ (v2_pre_topc @ X27)
% 0.22/0.53          | (v2_struct_0 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.53  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.53  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['6'])).
% 0.22/0.53  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('split', [status(esa)], ['8'])).
% 0.22/0.53  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.22/0.53      inference('split', [status(esa)], ['6'])).
% 0.22/0.53  thf(d1_xboole_0, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.53  thf(l1_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X4 : $i, X6 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf(t1_tex_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.53           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X24 : $i, X25 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X24)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X24)
% 0.22/0.53          | ((X25) = (X24))
% 0.22/0.53          | ~ (r1_tarski @ X25 @ X24)
% 0.22/0.53          | (v1_xboole_0 @ X25))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.22/0.53          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.22/0.53          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.22/0.53          | (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.53  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.22/0.53  thf('17', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X0)
% 0.22/0.53          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t4_subset, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X12 @ X13)
% 0.22/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.53          | (m1_subset_1 @ X12 @ X14))),
% 0.22/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.53        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.22/0.53  thf('24', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('25', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf(t36_tex_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X28 : $i, X29 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.22/0.53          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.22/0.53          | ~ (l1_pre_topc @ X29)
% 0.22/0.53          | ~ (v2_pre_topc @ X29)
% 0.22/0.53          | (v2_struct_0 @ X29))),
% 0.22/0.53      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.22/0.53           sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('30', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X19 : $i, X20 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X19)
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ X19)
% 0.22/0.53          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.22/0.53          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.22/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc1_subset_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.22/0.53          | (v1_xboole_0 @ X7)
% 0.22/0.53          | ~ (v1_xboole_0 @ X8))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.53  thf('36', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('37', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.22/0.53         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.22/0.53      inference('clc', [status(thm)], ['32', '37'])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['27', '28', '29', '38'])).
% 0.22/0.53  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('41', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.22/0.53      inference('clc', [status(thm)], ['39', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.53        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['18', '41'])).
% 0.22/0.53  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('44', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '44'])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['8'])).
% 0.22/0.53  thf('47', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.53  thf('48', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.22/0.53      inference('split', [status(esa)], ['6'])).
% 0.22/0.53  thf('49', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['9', '47', '48'])).
% 0.22/0.53  thf('50', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['7', '49'])).
% 0.22/0.53  thf('51', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['5', '50'])).
% 0.22/0.53  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['51', '52'])).
% 0.22/0.53  thf('54', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('55', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.22/0.53  thf('56', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X26)
% 0.22/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.53          | ~ (v2_tex_2 @ X26 @ X27)
% 0.22/0.53          | (m1_pre_topc @ (sk_C @ X26 @ X27) @ X27)
% 0.22/0.53          | ~ (l1_pre_topc @ X27)
% 0.22/0.53          | ~ (v2_pre_topc @ X27)
% 0.22/0.53          | (v2_struct_0 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.22/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.53  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('61', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['7', '49'])).
% 0.22/0.53  thf('62', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.22/0.53  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('64', plain,
% 0.22/0.53      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.53  thf('65', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('66', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.22/0.53      inference('clc', [status(thm)], ['64', '65'])).
% 0.22/0.53  thf(cc32_tex_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.22/0.53         ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.53           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.22/0.53             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.22/0.53  thf('67', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i]:
% 0.22/0.53         (~ (m1_pre_topc @ X22 @ X23)
% 0.22/0.53          | ~ (v1_tdlat_3 @ X22)
% 0.22/0.53          | (v7_struct_0 @ X22)
% 0.22/0.53          | (v2_struct_0 @ X22)
% 0.22/0.53          | ~ (l1_pre_topc @ X23)
% 0.22/0.53          | ~ (v2_tdlat_3 @ X23)
% 0.22/0.53          | ~ (v2_pre_topc @ X23)
% 0.22/0.53          | (v2_struct_0 @ X23))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53        | ~ (v2_tdlat_3 @ sk_A)
% 0.22/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.53  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('70', plain, ((v2_tdlat_3 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('72', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('73', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X26)
% 0.22/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.53          | ~ (v2_tex_2 @ X26 @ X27)
% 0.22/0.53          | (v1_tdlat_3 @ (sk_C @ X26 @ X27))
% 0.22/0.53          | ~ (l1_pre_topc @ X27)
% 0.22/0.53          | ~ (v2_pre_topc @ X27)
% 0.22/0.53          | (v2_struct_0 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.53  thf('74', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.53  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('77', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['7', '49'])).
% 0.22/0.53  thf('78', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.22/0.53  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('80', plain,
% 0.22/0.53      (((v1_xboole_0 @ sk_B_1) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['78', '79'])).
% 0.22/0.53  thf('81', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('82', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['80', '81'])).
% 0.22/0.53  thf('83', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('demod', [status(thm)], ['68', '69', '70', '71', '82'])).
% 0.22/0.53  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('85', plain,
% 0.22/0.53      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['83', '84'])).
% 0.22/0.53  thf('86', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('87', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X26)
% 0.22/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.53          | ~ (v2_tex_2 @ X26 @ X27)
% 0.22/0.53          | ((X26) = (u1_struct_0 @ (sk_C @ X26 @ X27)))
% 0.22/0.53          | ~ (l1_pre_topc @ X27)
% 0.22/0.53          | ~ (v2_pre_topc @ X27)
% 0.22/0.53          | (v2_struct_0 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.53  thf('88', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.53  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('91', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['7', '49'])).
% 0.22/0.53  thf('92', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.22/0.53  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('94', plain,
% 0.22/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.22/0.53      inference('clc', [status(thm)], ['92', '93'])).
% 0.22/0.53  thf('95', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('96', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['94', '95'])).
% 0.22/0.53  thf(fc7_struct_0, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.53       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.22/0.53  thf('97', plain,
% 0.22/0.53      (![X18 : $i]:
% 0.22/0.53         ((v1_zfmisc_1 @ (u1_struct_0 @ X18))
% 0.22/0.53          | ~ (l1_struct_0 @ X18)
% 0.22/0.53          | ~ (v7_struct_0 @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.22/0.53  thf('98', plain,
% 0.22/0.53      (((v1_zfmisc_1 @ sk_B_1)
% 0.22/0.53        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['96', '97'])).
% 0.22/0.53  thf('99', plain,
% 0.22/0.53      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.22/0.53      inference('split', [status(esa)], ['8'])).
% 0.22/0.53  thf('100', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['9', '47'])).
% 0.22/0.53  thf('101', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['99', '100'])).
% 0.22/0.53  thf('102', plain,
% 0.22/0.53      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.53        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['98', '101'])).
% 0.22/0.53  thf('103', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.22/0.53      inference('clc', [status(thm)], ['64', '65'])).
% 0.22/0.53  thf(dt_m1_pre_topc, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_pre_topc @ A ) =>
% 0.22/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.53  thf('104', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i]:
% 0.22/0.53         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.53          | (l1_pre_topc @ X16)
% 0.22/0.53          | ~ (l1_pre_topc @ X17))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.53  thf('105', plain,
% 0.22/0.53      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['103', '104'])).
% 0.22/0.53  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('107', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['105', '106'])).
% 0.22/0.53  thf(dt_l1_pre_topc, axiom,
% 0.22/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.53  thf('108', plain,
% 0.22/0.53      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.53  thf('109', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['107', '108'])).
% 0.22/0.53  thf('110', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['102', '109'])).
% 0.22/0.53  thf('111', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['85', '110'])).
% 0.22/0.53  thf('112', plain, ($false), inference('demod', [status(thm)], ['55', '111'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
