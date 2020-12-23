%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sEqAvz6PO7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:01 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  147 (1189 expanded)
%              Number of leaves         :   26 ( 345 expanded)
%              Depth                    :   24
%              Number of atoms          : 1128 (13237 expanded)
%              Number of equality atoms :   20 ( 424 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('20',plain,
    ( ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf(d3_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
             => ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X23 ) @ ( sk_B @ X23 ) ) @ ( u1_pre_topc @ X23 ) )
      | ( v3_tdlat_3 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('40',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('48',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

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

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_tops_2 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_tops_2 @ X15 @ X16 )
      | ( X15 != X13 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('50',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v1_tops_2 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_tops_2 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_A @ sk_B_1 )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('56',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ( v1_tops_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['62','64'])).

thf('66',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['52','53','54','55','65'])).

thf('67',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['46','66'])).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('72',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(fc5_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ) )).

thf('79',plain,(
    ! [X19: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc5_compts_1])).

thf('80',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('81',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('83',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v1_tops_2 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_tops_2 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ X1 )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','95'])).

thf('97',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','96'])).

thf('98',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','97'])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('100',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_tdlat_3 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('101',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_tdlat_3 @ X23 )
      | ~ ( r2_hidden @ X24 @ ( u1_pre_topc @ X23 ) )
      | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X23 ) @ X24 ) @ ( u1_pre_topc @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','96'])).

thf('112',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ ( sk_B @ X23 ) @ ( u1_pre_topc @ X23 ) )
      | ( v3_tdlat_3 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('113',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['110','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['98','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sEqAvz6PO7
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 102 iterations in 0.049s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.36/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.36/0.53  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.36/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.36/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.53  thf(t2_tsep_1, axiom,
% 0.36/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.36/0.53  thf('0', plain,
% 0.36/0.53      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.36/0.53      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.36/0.53  thf(t65_pre_topc, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( l1_pre_topc @ B ) =>
% 0.36/0.53           ( ( m1_pre_topc @ A @ B ) <=>
% 0.36/0.53             ( m1_pre_topc @
% 0.36/0.53               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X11)
% 0.36/0.53          | ~ (m1_pre_topc @ X12 @ X11)
% 0.36/0.53          | (m1_pre_topc @ X12 @ 
% 0.36/0.53             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.36/0.53          | ~ (l1_pre_topc @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X0)
% 0.36/0.53          | ~ (l1_pre_topc @ X0)
% 0.36/0.53          | (m1_pre_topc @ X0 @ 
% 0.36/0.53             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.36/0.53          | ~ (l1_pre_topc @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((m1_pre_topc @ X0 @ 
% 0.36/0.53           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.36/0.53          | ~ (l1_pre_topc @ X0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.53  thf(t19_tex_2, conjecture,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( l1_pre_topc @ B ) =>
% 0.36/0.53           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.36/0.53                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.36/0.53               ( v3_tdlat_3 @ A ) ) =>
% 0.36/0.53             ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i]:
% 0.36/0.53        ( ( l1_pre_topc @ A ) =>
% 0.36/0.53          ( ![B:$i]:
% 0.36/0.53            ( ( l1_pre_topc @ B ) =>
% 0.36/0.53              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.36/0.53                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.36/0.53                  ( v3_tdlat_3 @ A ) ) =>
% 0.36/0.53                ( v3_tdlat_3 @ B ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t19_tex_2])).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.36/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t59_pre_topc, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_pre_topc @
% 0.36/0.53             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.36/0.53           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      (![X9 : $i, X10 : $i]:
% 0.36/0.53         (~ (m1_pre_topc @ X9 @ 
% 0.36/0.53             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.36/0.53          | (m1_pre_topc @ X9 @ X10)
% 0.36/0.53          | ~ (l1_pre_topc @ X10))),
% 0.36/0.53      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.36/0.53  thf('6', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (m1_pre_topc @ X0 @ 
% 0.36/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.36/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.53  thf('7', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (m1_pre_topc @ X0 @ 
% 0.36/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.36/0.53          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.36/0.53  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['3', '8'])).
% 0.36/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('11', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.36/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.53  thf(t35_borsuk_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.53           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (![X21 : $i, X22 : $i]:
% 0.36/0.53         (~ (m1_pre_topc @ X21 @ X22)
% 0.36/0.53          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.36/0.53          | ~ (l1_pre_topc @ X22))),
% 0.36/0.53      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.36/0.53  thf('13', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.53  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.53  thf(d10_xboole_0, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X0 : $i, X2 : $i]:
% 0.36/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | ((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.36/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((m1_pre_topc @ X0 @ 
% 0.36/0.53           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.36/0.53          | ~ (l1_pre_topc @ X0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      (((m1_pre_topc @ sk_B_1 @ 
% 0.36/0.53         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_B_1))),
% 0.36/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.53  thf('21', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('22', plain,
% 0.36/0.53      ((m1_pre_topc @ sk_B_1 @ 
% 0.36/0.53        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      (![X9 : $i, X10 : $i]:
% 0.36/0.53         (~ (m1_pre_topc @ X9 @ 
% 0.36/0.53             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.36/0.53          | (m1_pre_topc @ X9 @ X10)
% 0.36/0.53          | ~ (l1_pre_topc @ X10))),
% 0.36/0.53      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.36/0.53  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.53  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('26', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('27', plain,
% 0.36/0.53      (![X21 : $i, X22 : $i]:
% 0.36/0.53         (~ (m1_pre_topc @ X21 @ X22)
% 0.36/0.53          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.36/0.53          | ~ (l1_pre_topc @ X22))),
% 0.36/0.53      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.36/0.53  thf('28', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.53  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.53  thf('31', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.36/0.53  thf(d3_tdlat_3, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ( v3_tdlat_3 @ A ) <=>
% 0.36/0.53         ( ![B:$i]:
% 0.36/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53             ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) =>
% 0.36/0.53               ( r2_hidden @
% 0.36/0.53                 ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.36/0.53                 ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      (![X23 : $i]:
% 0.36/0.53         (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X23) @ (sk_B @ X23)) @ 
% 0.36/0.53             (u1_pre_topc @ X23))
% 0.36/0.53          | (v3_tdlat_3 @ X23)
% 0.36/0.53          | ~ (l1_pre_topc @ X23))),
% 0.36/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.36/0.53  thf('33', plain,
% 0.36/0.53      ((~ (r2_hidden @ 
% 0.36/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.53           (u1_pre_topc @ sk_B_1))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.53  thf('34', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('35', plain,
% 0.36/0.53      ((~ (r2_hidden @ 
% 0.36/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.53           (u1_pre_topc @ sk_B_1))
% 0.36/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.53  thf('36', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('37', plain,
% 0.36/0.53      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.53          (u1_pre_topc @ sk_B_1))),
% 0.36/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.36/0.53  thf('38', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.36/0.53  thf(dt_u1_pre_topc, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( m1_subset_1 @
% 0.36/0.53         ( u1_pre_topc @ A ) @ 
% 0.36/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.53  thf('39', plain,
% 0.36/0.53      (![X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.36/0.53          | ~ (l1_pre_topc @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.53  thf('40', plain,
% 0.36/0.53      (((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.36/0.53         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_B_1))),
% 0.36/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.36/0.53  thf('41', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.53  thf(t78_tops_2, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @
% 0.36/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.53           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      (![X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X17 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.36/0.53          | ~ (v1_tops_2 @ X17 @ X18)
% 0.36/0.53          | (r1_tarski @ X17 @ (u1_pre_topc @ X18))
% 0.36/0.53          | ~ (l1_pre_topc @ X18))),
% 0.36/0.53      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.36/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.53  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      (((r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.36/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.53  thf('47', plain,
% 0.36/0.53      (![X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.36/0.53          | ~ (l1_pre_topc @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.53  thf(t35_tops_2, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @
% 0.36/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.53           ( ![C:$i]:
% 0.36/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.36/0.53               ( ( v1_tops_2 @ B @ A ) =>
% 0.36/0.53                 ( ![D:$i]:
% 0.36/0.53                   ( ( m1_subset_1 @
% 0.36/0.53                       D @ 
% 0.36/0.53                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.36/0.53                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X13 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.36/0.53          | ~ (v1_tops_2 @ X13 @ X14)
% 0.36/0.53          | ~ (m1_subset_1 @ X15 @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.36/0.53          | (v1_tops_2 @ X15 @ X16)
% 0.36/0.53          | ((X15) != (X13))
% 0.36/0.53          | ~ (m1_pre_topc @ X16 @ X14)
% 0.36/0.53          | ~ (l1_pre_topc @ X14))),
% 0.36/0.53      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X14)
% 0.36/0.53          | ~ (m1_pre_topc @ X16 @ X14)
% 0.36/0.53          | (v1_tops_2 @ X13 @ X16)
% 0.36/0.53          | ~ (m1_subset_1 @ X13 @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.36/0.53          | ~ (v1_tops_2 @ X13 @ X14)
% 0.36/0.53          | ~ (m1_subset_1 @ X13 @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))))),
% 0.36/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.36/0.53          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ X0)
% 0.36/0.53          | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.36/0.53          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.36/0.53          | ~ (l1_pre_topc @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['48', '50'])).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53        | ~ (m1_pre_topc @ sk_A @ sk_B_1)
% 0.36/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.36/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['47', '51'])).
% 0.36/0.53  thf('53', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('54', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('55', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.36/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.53  thf('56', plain,
% 0.36/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.53  thf('57', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.36/0.53  thf('58', plain,
% 0.36/0.53      (![X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X17 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.36/0.53          | ~ (r1_tarski @ X17 @ (u1_pre_topc @ X18))
% 0.36/0.53          | (v1_tops_2 @ X17 @ X18)
% 0.36/0.53          | ~ (l1_pre_topc @ X18))),
% 0.36/0.53      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.36/0.53  thf('59', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.36/0.53          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.53  thf('60', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('61', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.36/0.53          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.36/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.53  thf('62', plain,
% 0.36/0.53      ((~ (r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.36/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['56', '61'])).
% 0.36/0.53  thf('63', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.53      inference('simplify', [status(thm)], ['63'])).
% 0.36/0.53  thf('65', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1)),
% 0.36/0.53      inference('demod', [status(thm)], ['62', '64'])).
% 0.36/0.53  thf('66', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['52', '53', '54', '55', '65'])).
% 0.36/0.53  thf('67', plain,
% 0.36/0.53      ((r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['46', '66'])).
% 0.36/0.53  thf('68', plain,
% 0.36/0.53      (![X0 : $i, X2 : $i]:
% 0.36/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('69', plain,
% 0.36/0.53      ((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1))
% 0.36/0.53        | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.53  thf('70', plain,
% 0.36/0.53      (![X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.36/0.53          | ~ (l1_pre_topc @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.53  thf('71', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.36/0.53  thf('72', plain,
% 0.36/0.53      (![X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X17 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.36/0.53          | ~ (v1_tops_2 @ X17 @ X18)
% 0.36/0.53          | (r1_tarski @ X17 @ (u1_pre_topc @ X18))
% 0.36/0.53          | ~ (l1_pre_topc @ X18))),
% 0.36/0.53      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.36/0.53  thf('73', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.36/0.53          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.36/0.53  thf('74', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('75', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.36/0.53          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.36/0.53  thf('76', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.36/0.53        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['70', '75'])).
% 0.36/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('78', plain,
% 0.36/0.53      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.36/0.53        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1)))),
% 0.36/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.36/0.53  thf(fc5_compts_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ))).
% 0.36/0.53  thf('79', plain,
% 0.36/0.53      (![X19 : $i]:
% 0.36/0.53         ((v1_tops_2 @ (u1_pre_topc @ X19) @ X19) | ~ (l1_pre_topc @ X19))),
% 0.36/0.53      inference('cnf', [status(esa)], [fc5_compts_1])).
% 0.36/0.53  thf('80', plain,
% 0.36/0.53      (![X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.36/0.53          | ~ (l1_pre_topc @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.53  thf('81', plain,
% 0.36/0.53      (![X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.36/0.53          | ~ (l1_pre_topc @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.53  thf('82', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.36/0.53  thf('83', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X14)
% 0.36/0.53          | ~ (m1_pre_topc @ X16 @ X14)
% 0.36/0.53          | (v1_tops_2 @ X13 @ X16)
% 0.36/0.53          | ~ (m1_subset_1 @ X13 @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.36/0.53          | ~ (v1_tops_2 @ X13 @ X14)
% 0.36/0.53          | ~ (m1_subset_1 @ X13 @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))))),
% 0.36/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.53  thf('84', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.36/0.53          | ~ (v1_tops_2 @ X0 @ X1)
% 0.36/0.53          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.36/0.53          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 0.36/0.53          | ~ (l1_pre_topc @ X1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['82', '83'])).
% 0.36/0.53  thf('85', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | ~ (l1_pre_topc @ X0)
% 0.36/0.53          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.36/0.53          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.36/0.53          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.36/0.53          | ~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['81', '84'])).
% 0.36/0.53  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('87', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X0)
% 0.36/0.53          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.36/0.53          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.36/0.53          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.36/0.53          | ~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.36/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.36/0.53      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.53  thf('88', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.36/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.36/0.53        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['80', '87'])).
% 0.36/0.53  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('90', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('92', plain,
% 0.36/0.53      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.36/0.53        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.36/0.53  thf('93', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A) | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['79', '92'])).
% 0.36/0.53  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('95', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)),
% 0.36/0.53      inference('demod', [status(thm)], ['93', '94'])).
% 0.36/0.53  thf('96', plain,
% 0.36/0.53      ((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['78', '95'])).
% 0.36/0.53  thf('97', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['69', '96'])).
% 0.36/0.53  thf('98', plain,
% 0.36/0.53      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.53          (u1_pre_topc @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['37', '97'])).
% 0.36/0.53  thf('99', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.36/0.53  thf('100', plain,
% 0.36/0.53      (![X23 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (sk_B @ X23) @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.36/0.53          | (v3_tdlat_3 @ X23)
% 0.36/0.53          | ~ (l1_pre_topc @ X23))),
% 0.36/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.36/0.53  thf('101', plain,
% 0.36/0.53      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.36/0.53      inference('sup+', [status(thm)], ['99', '100'])).
% 0.36/0.53  thf('102', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('103', plain,
% 0.36/0.53      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['101', '102'])).
% 0.36/0.53  thf('104', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('105', plain,
% 0.36/0.53      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('clc', [status(thm)], ['103', '104'])).
% 0.36/0.53  thf('106', plain,
% 0.36/0.53      (![X23 : $i, X24 : $i]:
% 0.36/0.53         (~ (v3_tdlat_3 @ X23)
% 0.36/0.53          | ~ (r2_hidden @ X24 @ (u1_pre_topc @ X23))
% 0.36/0.53          | (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X23) @ X24) @ 
% 0.36/0.53             (u1_pre_topc @ X23))
% 0.36/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.36/0.53          | ~ (l1_pre_topc @ X23))),
% 0.36/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.36/0.53  thf('107', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (r2_hidden @ 
% 0.36/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.53           (u1_pre_topc @ sk_A))
% 0.36/0.53        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.36/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['105', '106'])).
% 0.36/0.53  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('109', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('110', plain,
% 0.36/0.53      (((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.53         (u1_pre_topc @ sk_A))
% 0.36/0.53        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.36/0.53  thf('111', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['69', '96'])).
% 0.36/0.53  thf('112', plain,
% 0.36/0.53      (![X23 : $i]:
% 0.36/0.53         ((r2_hidden @ (sk_B @ X23) @ (u1_pre_topc @ X23))
% 0.36/0.53          | (v3_tdlat_3 @ X23)
% 0.36/0.53          | ~ (l1_pre_topc @ X23))),
% 0.36/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.36/0.53  thf('113', plain,
% 0.36/0.53      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.36/0.53      inference('sup+', [status(thm)], ['111', '112'])).
% 0.36/0.53  thf('114', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('115', plain,
% 0.36/0.53      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.36/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['113', '114'])).
% 0.36/0.53  thf('116', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('117', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.36/0.53      inference('clc', [status(thm)], ['115', '116'])).
% 0.36/0.53  thf('118', plain,
% 0.36/0.53      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.53        (u1_pre_topc @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['110', '117'])).
% 0.36/0.53  thf('119', plain, ($false), inference('demod', [status(thm)], ['98', '118'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
