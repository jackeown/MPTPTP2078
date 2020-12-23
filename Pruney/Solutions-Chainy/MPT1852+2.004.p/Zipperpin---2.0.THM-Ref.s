%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v4AOz62rgD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  168 (2059 expanded)
%              Number of leaves         :   27 ( 597 expanded)
%              Depth                    :   24
%              Number of atoms          : 1288 (22799 expanded)
%              Number of equality atoms :   21 ( 690 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t19_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v3_tdlat_3 @ A ) )
           => ( v3_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v3_tdlat_3 @ A ) )
             => ( v3_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_tex_2])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( m1_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('22',plain,
    ( ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( m1_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf(d3_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
             => ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X29 ) @ ( sk_B @ X29 ) ) @ ( u1_pre_topc @ X29 ) )
      | ( v3_tdlat_3 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('37',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('44',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('53',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_tops_2 @ X23 @ X24 )
      | ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('59',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t35_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ( v1_tops_2 @ X21 @ X22 )
      | ( X21 != X19 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v1_tops_2 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_A @ sk_B_1 )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('67',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('69',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( v1_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['73','75'])).

thf('77',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66','76'])).

thf('78',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['57','77'])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('88',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_tops_2 @ X23 @ X24 )
      | ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('96',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('98',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v1_tops_2 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ X1 )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('104',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( v1_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('108',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['101','102','108','109','110'])).

thf('112',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['94','111'])).

thf('113',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','112'])).

thf('114',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','113'])).

thf('115',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('116',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_tdlat_3 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('117',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tdlat_3 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r1_tarski @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r1_tarski @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    r1_tarski @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('125',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_tdlat_3 @ X29 )
      | ~ ( r2_hidden @ X30 @ ( u1_pre_topc @ X29 ) )
      | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X29 ) @ X30 ) @ ( u1_pre_topc @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','112'])).

thf('132',plain,(
    ! [X29: $i] :
      ( ( r2_hidden @ ( sk_B @ X29 ) @ ( u1_pre_topc @ X29 ) )
      | ( v3_tdlat_3 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('133',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['130','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['114','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v4AOz62rgD
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:02:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 198 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.53  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(t2_tsep_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.53  thf(t65_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( l1_pre_topc @ B ) =>
% 0.21/0.53           ( ( m1_pre_topc @ A @ B ) <=>
% 0.21/0.53             ( m1_pre_topc @
% 0.21/0.53               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X14)
% 0.21/0.53          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.53          | (m1_pre_topc @ X15 @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 0.21/0.53          | ~ (l1_pre_topc @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (m1_pre_topc @ X0 @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m1_pre_topc @ X0 @ 
% 0.21/0.53           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf(t19_tex_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( l1_pre_topc @ B ) =>
% 0.21/0.53           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.53                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.53               ( v3_tdlat_3 @ A ) ) =>
% 0.21/0.53             ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( l1_pre_topc @ A ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( l1_pre_topc @ B ) =>
% 0.21/0.53              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.53                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.53                  ( v3_tdlat_3 @ A ) ) =>
% 0.21/0.53                ( v3_tdlat_3 @ B ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t19_tex_2])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t59_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @
% 0.21/0.53             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.53           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X12 @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.21/0.53          | (m1_pre_topc @ X12 @ X13)
% 0.21/0.53          | ~ (l1_pre_topc @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.53          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(t1_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( m1_subset_1 @
% 0.21/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X26 @ X27)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.53          | ~ (l1_pre_topc @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m1_pre_topc @ X0 @ 
% 0.21/0.53           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_B_1 @ 
% 0.21/0.53         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((m1_pre_topc @ sk_B_1 @ 
% 0.21/0.53        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X12 @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.21/0.53          | (m1_pre_topc @ X12 @ X13)
% 0.21/0.53          | ~ (l1_pre_topc @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.53  thf('26', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X26 @ X27)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.53          | ~ (l1_pre_topc @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '34'])).
% 0.21/0.53  thf(d3_tdlat_3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.53         ( ![B:$i]:
% 0.21/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53             ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) =>
% 0.21/0.53               ( r2_hidden @
% 0.21/0.53                 ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.53                 ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X29 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X29) @ (sk_B @ X29)) @ 
% 0.21/0.53             (u1_pre_topc @ X29))
% 0.21/0.53          | (v3_tdlat_3 @ X29)
% 0.21/0.53          | ~ (l1_pre_topc @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((~ (r2_hidden @ 
% 0.21/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53           (u1_pre_topc @ sk_B_1))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((~ (r2_hidden @ 
% 0.21/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53           (u1_pre_topc @ sk_B_1))
% 0.21/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53          (u1_pre_topc @ sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      ((m1_pre_topc @ sk_B_1 @ 
% 0.21/0.53        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.53          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('44', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf(dt_u1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( m1_subset_1 @
% 0.21/0.53         ( u1_pre_topc @ A ) @ 
% 0.21/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X8 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.53          | ~ (l1_pre_topc @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.53  thf(t31_tops_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @
% 0.21/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.53               ( m1_subset_1 @
% 0.21/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.53          | (m1_subset_1 @ X18 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.21/0.53          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.21/0.53          | ~ (l1_pre_topc @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X1)
% 0.21/0.53          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.53  thf('49', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.53  thf('52', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '34'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf(t78_tops_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @
% 0.21/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.21/0.53          | ~ (v1_tops_2 @ X23 @ X24)
% 0.21/0.53          | (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.21/0.53          | ~ (l1_pre_topc @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (((r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X8 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.53          | ~ (l1_pre_topc @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf(t35_tops_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @
% 0.21/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.53               ( ( v1_tops_2 @ B @ A ) =>
% 0.21/0.53                 ( ![D:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @
% 0.21/0.53                       D @ 
% 0.21/0.53                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.21/0.53                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X19 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.21/0.53          | ~ (v1_tops_2 @ X19 @ X20)
% 0.21/0.53          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.21/0.53          | (v1_tops_2 @ X21 @ X22)
% 0.21/0.53          | ((X21) != (X19))
% 0.21/0.53          | ~ (m1_pre_topc @ X22 @ X20)
% 0.21/0.53          | ~ (l1_pre_topc @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X20)
% 0.21/0.53          | ~ (m1_pre_topc @ X22 @ X20)
% 0.21/0.53          | (v1_tops_2 @ X19 @ X22)
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.21/0.53          | ~ (v1_tops_2 @ X19 @ X20)
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.53          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ X0)
% 0.21/0.53          | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['59', '61'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | ~ (m1_pre_topc @ sk_A @ sk_B_1)
% 0.21/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.21/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['58', '62'])).
% 0.21/0.53  thf('64', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('65', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('68', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '34'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.21/0.53          | ~ (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.21/0.53          | (v1_tops_2 @ X23 @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.53  thf('71', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((~ (r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.21/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['67', '72'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.53  thf('76', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['73', '75'])).
% 0.21/0.53  thf('77', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['63', '64', '65', '66', '76'])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      ((r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['57', '77'])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1))
% 0.21/0.53        | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X1)
% 0.21/0.53          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.53  thf('84', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.53      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.21/0.53  thf('87', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '34'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.53  thf('89', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '34'])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.21/0.53          | ~ (v1_tops_2 @ X23 @ X24)
% 0.21/0.53          | (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.21/0.53          | ~ (l1_pre_topc @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.21/0.53          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.53  thf('92', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.21/0.53          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.21/0.53        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['88', '93'])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      (![X8 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.53          | ~ (l1_pre_topc @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.53  thf('97', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '34'])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X20)
% 0.21/0.53          | ~ (m1_pre_topc @ X22 @ X20)
% 0.21/0.53          | (v1_tops_2 @ X19 @ X22)
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.21/0.53          | ~ (v1_tops_2 @ X19 @ X20)
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.53  thf('99', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.53          | ~ (v1_tops_2 @ X0 @ X1)
% 0.21/0.53          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 0.21/0.53          | ~ (l1_pre_topc @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.53  thf('100', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.21/0.53          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.21/0.53          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['96', '99'])).
% 0.21/0.53  thf('101', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.21/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.21/0.53        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['95', '100'])).
% 0.21/0.53  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.53  thf('104', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.21/0.53          | ~ (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.21/0.53          | (v1_tops_2 @ X23 @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.53  thf('105', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.21/0.53        | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.53  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('107', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.53  thf('108', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.21/0.53  thf('109', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('111', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['101', '102', '108', '109', '110'])).
% 0.21/0.53  thf('112', plain,
% 0.21/0.53      ((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['94', '111'])).
% 0.21/0.53  thf('113', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['80', '112'])).
% 0.21/0.53  thf('114', plain,
% 0.21/0.53      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53          (u1_pre_topc @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '113'])).
% 0.21/0.53  thf('115', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '34'])).
% 0.21/0.53  thf('116', plain,
% 0.21/0.53      (![X29 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (sk_B @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.53          | (v3_tdlat_3 @ X29)
% 0.21/0.53          | ~ (l1_pre_topc @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.53  thf('117', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('118', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v3_tdlat_3 @ X0)
% 0.21/0.53          | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['116', '117'])).
% 0.21/0.53  thf('119', plain,
% 0.21/0.53      (((r1_tarski @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v3_tdlat_3 @ sk_B_1)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['115', '118'])).
% 0.21/0.53  thf('120', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('121', plain,
% 0.21/0.53      (((r1_tarski @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['119', '120'])).
% 0.21/0.53  thf('122', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('123', plain, ((r1_tarski @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['121', '122'])).
% 0.21/0.53  thf('124', plain,
% 0.21/0.53      (![X3 : $i, X5 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('125', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['123', '124'])).
% 0.21/0.53  thf('126', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v3_tdlat_3 @ X29)
% 0.21/0.53          | ~ (r2_hidden @ X30 @ (u1_pre_topc @ X29))
% 0.21/0.53          | (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X29) @ X30) @ 
% 0.21/0.53             (u1_pre_topc @ X29))
% 0.21/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.53          | ~ (l1_pre_topc @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.53  thf('127', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (r2_hidden @ 
% 0.21/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53           (u1_pre_topc @ sk_A))
% 0.21/0.53        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.53  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('129', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('130', plain,
% 0.21/0.53      (((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53         (u1_pre_topc @ sk_A))
% 0.21/0.53        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.21/0.53  thf('131', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['80', '112'])).
% 0.21/0.53  thf('132', plain,
% 0.21/0.53      (![X29 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_B @ X29) @ (u1_pre_topc @ X29))
% 0.21/0.53          | (v3_tdlat_3 @ X29)
% 0.21/0.53          | ~ (l1_pre_topc @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.53  thf('133', plain,
% 0.21/0.53      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['131', '132'])).
% 0.21/0.53  thf('134', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('135', plain,
% 0.21/0.53      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['133', '134'])).
% 0.21/0.53  thf('136', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('137', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['135', '136'])).
% 0.21/0.53  thf('138', plain,
% 0.21/0.53      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53        (u1_pre_topc @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['130', '137'])).
% 0.21/0.53  thf('139', plain, ($false), inference('demod', [status(thm)], ['114', '138'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
