%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3mwGAXPK2v

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:00 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  212 (2220 expanded)
%              Number of leaves         :   31 ( 640 expanded)
%              Depth                    :   27
%              Number of atoms          : 1759 (25163 expanded)
%              Number of equality atoms :   18 ( 779 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

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

thf('0',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( r1_tarski @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
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
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( r1_tarski @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
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
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_tdlat_3 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_tdlat_3 @ X32 )
      | ~ ( r2_hidden @ X33 @ ( u1_pre_topc @ X32 ) )
      | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X32 ) @ X33 ) @ ( u1_pre_topc @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X32: $i] :
      ( ( r2_hidden @ ( sk_B @ X32 ) @ ( u1_pre_topc @ X32 ) )
      | ( v3_tdlat_3 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('61',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['58','65'])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v3_tdlat_3 @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','71'])).

thf('73',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_tops_2 @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(fc5_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ) )).

thf('78',plain,(
    ! [X28: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_compts_1])).

thf('79',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('80',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

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

thf('81',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_tops_2 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( v1_tops_2 @ X26 @ X27 )
      | ( X26 != X24 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('82',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v1_tops_2 @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_tops_2 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_A @ sk_B_1 )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('88',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['77','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['72','94'])).

thf('96',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['45','95'])).

thf('97',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','96','97'])).

thf('99',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('121',plain,
    ( ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('123',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X32 ) @ ( sk_B @ X32 ) ) @ ( u1_pre_topc @ X32 ) )
      | ( v3_tdlat_3 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('124',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['121','128'])).

thf('130',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','96','97'])).

thf('131',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('132',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('133',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_tops_2 @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v3_pre_topc @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('142',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('143',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('144',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v1_tops_2 @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_tops_2 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ X1 )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('150',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( v1_tops_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( u1_pre_topc @ sk_A ) @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( u1_pre_topc @ sk_A ) @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X28: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_compts_1])).

thf('155',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('156',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_tops_2 @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['153','164'])).

thf('166',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('167',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X18 @ X19 ) @ X19 )
      | ( v1_tops_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('168',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['165','170'])).

thf('172',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['147','148','171','172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['140','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['130','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['129','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3mwGAXPK2v
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:42:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 245 iterations in 0.124s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.41/0.60  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.60  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.41/0.60  thf(t19_tex_2, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( l1_pre_topc @ B ) =>
% 0.41/0.60           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.41/0.60                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.41/0.60               ( v3_tdlat_3 @ A ) ) =>
% 0.41/0.60             ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( l1_pre_topc @ A ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( l1_pre_topc @ B ) =>
% 0.41/0.60              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.41/0.60                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.41/0.60                  ( v3_tdlat_3 @ A ) ) =>
% 0.41/0.60                ( v3_tdlat_3 @ B ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t19_tex_2])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.60         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t2_tsep_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.60  thf(t65_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( l1_pre_topc @ B ) =>
% 0.41/0.60           ( ( m1_pre_topc @ A @ B ) <=>
% 0.41/0.60             ( m1_pre_topc @
% 0.41/0.60               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X16)
% 0.41/0.60          | ~ (m1_pre_topc @ X17 @ X16)
% 0.41/0.60          | (m1_pre_topc @ X17 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.41/0.60          | ~ (l1_pre_topc @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | (m1_pre_topc @ X0 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_pre_topc @ X0 @ 
% 0.41/0.60           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (((m1_pre_topc @ sk_B_1 @ 
% 0.41/0.60         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B_1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['0', '4'])).
% 0.41/0.60  thf('6', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((m1_pre_topc @ sk_B_1 @ 
% 0.41/0.60        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf(t59_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @
% 0.41/0.60             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.41/0.60           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X14 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.41/0.60          | (m1_pre_topc @ X14 @ X15)
% 0.41/0.60          | ~ (l1_pre_topc @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.41/0.60  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('11', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf(t35_borsuk_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.60           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X30 @ X31)
% 0.41/0.60          | (r1_tarski @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 0.41/0.60          | ~ (l1_pre_topc @ X31))),
% 0.41/0.60      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X0 : $i, X2 : $i]:
% 0.41/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.41/0.60        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_pre_topc @ X0 @ 
% 0.41/0.60           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.60         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X14 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.41/0.60          | (m1_pre_topc @ X14 @ X15)
% 0.41/0.60          | ~ (l1_pre_topc @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X0 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('22', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X0 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.41/0.60          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '23'])).
% 0.41/0.60  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('26', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X30 @ X31)
% 0.41/0.60          | (r1_tarski @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 0.41/0.60          | ~ (l1_pre_topc @ X31))),
% 0.41/0.60      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf(d3_tdlat_3, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ( v3_tdlat_3 @ A ) <=>
% 0.41/0.60         ( ![B:$i]:
% 0.41/0.60           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60             ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) =>
% 0.41/0.60               ( r2_hidden @
% 0.41/0.60                 ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.41/0.60                 ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X32 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (sk_B @ X32) @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.41/0.60          | (v3_tdlat_3 @ X32)
% 0.41/0.60          | ~ (l1_pre_topc @ X32))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60        | (v3_tdlat_3 @ sk_B_1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.41/0.60  thf('34', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60        | (v3_tdlat_3 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X32 : $i, X33 : $i]:
% 0.41/0.60         (~ (v3_tdlat_3 @ X32)
% 0.41/0.60          | ~ (r2_hidden @ X33 @ (u1_pre_topc @ X32))
% 0.41/0.60          | (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X32) @ X33) @ 
% 0.41/0.60             (u1_pre_topc @ X32))
% 0.41/0.60          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.41/0.60          | ~ (l1_pre_topc @ X32))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60           (u1_pre_topc @ sk_A))
% 0.41/0.60        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.41/0.60        | ~ (v3_tdlat_3 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.60  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf(d5_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( v3_pre_topc @ B @ A ) <=>
% 0.41/0.60             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.41/0.60          | ~ (v3_pre_topc @ X6 @ X7)
% 0.41/0.60          | (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.41/0.60          | ~ (l1_pre_topc @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.41/0.60        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.41/0.60        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('47', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.41/0.60          | ~ (v3_pre_topc @ X6 @ X7)
% 0.41/0.60          | (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.41/0.60          | ~ (l1_pre_topc @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.41/0.60          | ~ (v3_pre_topc @ X0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.60  thf('50', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.41/0.60          | ~ (v3_pre_topc @ X0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['49', '50'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      ((~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1)
% 0.41/0.60        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['46', '51'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X32 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_B @ X32) @ (u1_pre_topc @ X32))
% 0.41/0.60          | (v3_tdlat_3 @ X32)
% 0.41/0.60          | ~ (l1_pre_topc @ X32))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.41/0.60  thf('54', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.41/0.60          | ~ (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.41/0.60          | (v3_pre_topc @ X6 @ X7)
% 0.41/0.60          | ~ (l1_pre_topc @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.60  thf('57', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.41/0.60  thf('59', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf(dt_u1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( m1_subset_1 @
% 0.41/0.60         ( u1_pre_topc @ A ) @ 
% 0.41/0.60         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.41/0.60          | ~ (l1_pre_topc @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.41/0.60         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B_1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['59', '60'])).
% 0.41/0.60  thf('62', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['61', '62'])).
% 0.41/0.60  thf(t4_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.60       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X3 @ X4)
% 0.41/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.41/0.60          | (m1_subset_1 @ X3 @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_B_1))),
% 0.41/0.60      inference('clc', [status(thm)], ['58', '65'])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60        | (v3_tdlat_3 @ sk_B_1)
% 0.41/0.60        | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['53', '66'])).
% 0.41/0.60  thf('68', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      (((v3_tdlat_3 @ sk_B_1) | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['67', '68'])).
% 0.41/0.60  thf('70', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('71', plain, ((v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.41/0.60      inference('clc', [status(thm)], ['69', '70'])).
% 0.41/0.60  thf('72', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['52', '71'])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['61', '62'])).
% 0.41/0.60  thf(d1_tops_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @
% 0.41/0.60             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60           ( ( v1_tops_2 @ B @ A ) <=>
% 0.41/0.60             ( ![C:$i]:
% 0.41/0.60               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X18 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.41/0.60          | ~ (v1_tops_2 @ X18 @ X19)
% 0.41/0.60          | ~ (r2_hidden @ X20 @ X18)
% 0.41/0.60          | (v3_pre_topc @ X20 @ X19)
% 0.41/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.60          | ~ (l1_pre_topc @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.41/0.60  thf('75', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.41/0.60          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.41/0.60  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('77', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.41/0.60          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.41/0.60  thf(fc5_compts_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ))).
% 0.41/0.60  thf('78', plain,
% 0.41/0.60      (![X28 : $i]:
% 0.41/0.60         ((v1_tops_2 @ (u1_pre_topc @ X28) @ X28) | ~ (l1_pre_topc @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc5_compts_1])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.41/0.60          | ~ (l1_pre_topc @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.60  thf('80', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['61', '62'])).
% 0.41/0.60  thf(t35_tops_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @
% 0.41/0.60             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.60               ( ( v1_tops_2 @ B @ A ) =>
% 0.41/0.60                 ( ![D:$i]:
% 0.41/0.60                   ( ( m1_subset_1 @
% 0.41/0.60                       D @ 
% 0.41/0.60                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.41/0.60                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X24 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))
% 0.41/0.60          | ~ (v1_tops_2 @ X24 @ X25)
% 0.41/0.60          | ~ (m1_subset_1 @ X26 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 0.41/0.60          | (v1_tops_2 @ X26 @ X27)
% 0.41/0.60          | ((X26) != (X24))
% 0.41/0.60          | ~ (m1_pre_topc @ X27 @ X25)
% 0.41/0.60          | ~ (l1_pre_topc @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.41/0.60  thf('82', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X27 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X25)
% 0.41/0.60          | ~ (m1_pre_topc @ X27 @ X25)
% 0.41/0.60          | (v1_tops_2 @ X24 @ X27)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 0.41/0.60          | ~ (v1_tops_2 @ X24 @ X25)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['81'])).
% 0.41/0.60  thf('83', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.41/0.60          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ X0)
% 0.41/0.60          | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.41/0.60          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['80', '82'])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60        | ~ (m1_pre_topc @ sk_A @ sk_B_1)
% 0.41/0.60        | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.41/0.60        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['79', '83'])).
% 0.41/0.60  thf('85', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('86', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('87', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      (((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.41/0.60        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.41/0.60  thf('89', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_B_1) | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['78', '88'])).
% 0.41/0.60  thf('90', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('91', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)),
% 0.41/0.60      inference('demod', [status(thm)], ['89', '90'])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['77', '91'])).
% 0.41/0.60  thf('93', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.60  thf('94', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['92', '93'])).
% 0.41/0.60  thf('95', plain, ((v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A)),
% 0.41/0.60      inference('sup-', [status(thm)], ['72', '94'])).
% 0.41/0.60  thf('96', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['45', '95'])).
% 0.41/0.60  thf('97', plain, ((v3_tdlat_3 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('98', plain,
% 0.41/0.60      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60        (u1_pre_topc @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['39', '40', '96', '97'])).
% 0.41/0.60  thf('99', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('100', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X16)
% 0.41/0.60          | ~ (m1_pre_topc @ X17 @ X16)
% 0.41/0.60          | (m1_pre_topc @ X17 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.41/0.60          | ~ (l1_pre_topc @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.41/0.60  thf('101', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (m1_pre_topc @ sk_A @ 
% 0.41/0.60           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['99', '100'])).
% 0.41/0.60  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('103', plain,
% 0.41/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.60         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('104', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('105', plain,
% 0.41/0.60      ((m1_pre_topc @ sk_A @ 
% 0.41/0.60        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.41/0.60  thf('106', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X14 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.41/0.60          | (m1_pre_topc @ X14 @ X15)
% 0.41/0.60          | ~ (l1_pre_topc @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.41/0.60  thf('107', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['105', '106'])).
% 0.41/0.60  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('109', plain, ((m1_pre_topc @ sk_A @ sk_A)),
% 0.41/0.60      inference('demod', [status(thm)], ['107', '108'])).
% 0.41/0.60  thf('110', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.41/0.60          | ~ (l1_pre_topc @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.60  thf(t31_tops_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @
% 0.41/0.60                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.41/0.60               ( m1_subset_1 @
% 0.41/0.60                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('111', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X21 @ X22)
% 0.41/0.60          | (m1_subset_1 @ X23 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.41/0.60          | ~ (m1_subset_1 @ X23 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.41/0.60          | ~ (l1_pre_topc @ X22))),
% 0.41/0.60      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.41/0.60  thf('112', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X1)
% 0.41/0.60          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['110', '111'])).
% 0.41/0.60  thf('113', plain,
% 0.41/0.60      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.60         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['109', '112'])).
% 0.41/0.60  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('116', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.41/0.60  thf('117', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X3 @ X4)
% 0.41/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.41/0.60          | (m1_subset_1 @ X3 @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.60  thf('118', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['116', '117'])).
% 0.41/0.60  thf('119', plain,
% 0.41/0.60      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['98', '118'])).
% 0.41/0.60  thf('120', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.41/0.60          | ~ (v3_pre_topc @ X0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['49', '50'])).
% 0.41/0.60  thf('121', plain,
% 0.41/0.60      ((~ (v3_pre_topc @ 
% 0.41/0.60           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60           (u1_pre_topc @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['119', '120'])).
% 0.41/0.60  thf('122', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf('123', plain,
% 0.41/0.60      (![X32 : $i]:
% 0.41/0.60         (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X32) @ (sk_B @ X32)) @ 
% 0.41/0.60             (u1_pre_topc @ X32))
% 0.41/0.60          | (v3_tdlat_3 @ X32)
% 0.41/0.60          | ~ (l1_pre_topc @ X32))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.41/0.60  thf('124', plain,
% 0.41/0.60      ((~ (r2_hidden @ 
% 0.41/0.60           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60           (u1_pre_topc @ sk_B_1))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60        | (v3_tdlat_3 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['122', '123'])).
% 0.41/0.60  thf('125', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('126', plain,
% 0.41/0.60      ((~ (r2_hidden @ 
% 0.41/0.60           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60           (u1_pre_topc @ sk_B_1))
% 0.41/0.60        | (v3_tdlat_3 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['124', '125'])).
% 0.41/0.60  thf('127', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('128', plain,
% 0.41/0.60      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60          (u1_pre_topc @ sk_B_1))),
% 0.41/0.60      inference('clc', [status(thm)], ['126', '127'])).
% 0.41/0.60  thf('129', plain,
% 0.41/0.60      (~ (v3_pre_topc @ 
% 0.41/0.60          (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 0.41/0.60      inference('clc', [status(thm)], ['121', '128'])).
% 0.41/0.60  thf('130', plain,
% 0.41/0.60      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60        (u1_pre_topc @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['39', '40', '96', '97'])).
% 0.41/0.60  thf('131', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.41/0.60          | ~ (l1_pre_topc @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.60  thf('132', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf('133', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X18 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.41/0.60          | ~ (v1_tops_2 @ X18 @ X19)
% 0.41/0.60          | ~ (r2_hidden @ X20 @ X18)
% 0.41/0.60          | (v3_pre_topc @ X20 @ X19)
% 0.41/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.60          | ~ (l1_pre_topc @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.41/0.60  thf('134', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.60          | (v3_pre_topc @ X1 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X1 @ X0)
% 0.41/0.60          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['132', '133'])).
% 0.41/0.60  thf('135', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('136', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf('137', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v3_pre_topc @ X1 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X1 @ X0)
% 0.41/0.60          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.41/0.60  thf('138', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ sk_A)
% 0.41/0.60          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['131', '137'])).
% 0.41/0.60  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('140', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['138', '139'])).
% 0.41/0.60  thf('141', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.41/0.60          | ~ (l1_pre_topc @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.60  thf('142', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.41/0.60  thf('143', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '30'])).
% 0.41/0.60  thf('144', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X27 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X25)
% 0.41/0.60          | ~ (m1_pre_topc @ X27 @ X25)
% 0.41/0.60          | (v1_tops_2 @ X24 @ X27)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 0.41/0.60          | ~ (v1_tops_2 @ X24 @ X25)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['81'])).
% 0.41/0.60  thf('145', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.41/0.60          | ~ (v1_tops_2 @ X0 @ X1)
% 0.41/0.60          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 0.41/0.60          | ~ (l1_pre_topc @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['143', '144'])).
% 0.41/0.60  thf('146', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.41/0.60          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.41/0.60          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['142', '145'])).
% 0.41/0.60  thf('147', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.41/0.60        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.41/0.60        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['141', '146'])).
% 0.41/0.60  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('149', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.41/0.60  thf('150', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X18 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.41/0.60          | (r2_hidden @ (sk_C @ X18 @ X19) @ X18)
% 0.41/0.60          | (v1_tops_2 @ X18 @ X19)
% 0.41/0.60          | ~ (l1_pre_topc @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.41/0.60  thf('151', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.41/0.60        | (r2_hidden @ (sk_C @ (u1_pre_topc @ sk_A) @ sk_A) @ 
% 0.41/0.60           (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['149', '150'])).
% 0.41/0.60  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('153', plain,
% 0.41/0.60      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.41/0.60        | (r2_hidden @ (sk_C @ (u1_pre_topc @ sk_A) @ sk_A) @ 
% 0.41/0.60           (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['151', '152'])).
% 0.41/0.60  thf('154', plain,
% 0.41/0.60      (![X28 : $i]:
% 0.41/0.60         ((v1_tops_2 @ (u1_pre_topc @ X28) @ X28) | ~ (l1_pre_topc @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc5_compts_1])).
% 0.41/0.60  thf('155', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.41/0.60  thf('156', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X18 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.41/0.60          | ~ (v1_tops_2 @ X18 @ X19)
% 0.41/0.60          | ~ (r2_hidden @ X20 @ X18)
% 0.41/0.60          | (v3_pre_topc @ X20 @ X19)
% 0.41/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.60          | ~ (l1_pre_topc @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.41/0.60  thf('157', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.41/0.60          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['155', '156'])).
% 0.41/0.60  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('159', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.41/0.60          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['157', '158'])).
% 0.41/0.60  thf('160', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['154', '159'])).
% 0.41/0.60  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('162', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['160', '161'])).
% 0.41/0.60  thf('163', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['116', '117'])).
% 0.41/0.60  thf('164', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v3_pre_topc @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['162', '163'])).
% 0.41/0.60  thf('165', plain,
% 0.41/0.60      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.41/0.60        | (v3_pre_topc @ (sk_C @ (u1_pre_topc @ sk_A) @ sk_A) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['153', '164'])).
% 0.41/0.60  thf('166', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.41/0.60  thf('167', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X18 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.41/0.60          | ~ (v3_pre_topc @ (sk_C @ X18 @ X19) @ X19)
% 0.41/0.60          | (v1_tops_2 @ X18 @ X19)
% 0.41/0.60          | ~ (l1_pre_topc @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.41/0.60  thf('168', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.41/0.60        | ~ (v3_pre_topc @ (sk_C @ (u1_pre_topc @ sk_A) @ sk_A) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['166', '167'])).
% 0.41/0.60  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('170', plain,
% 0.41/0.60      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.41/0.60        | ~ (v3_pre_topc @ (sk_C @ (u1_pre_topc @ sk_A) @ sk_A) @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['168', '169'])).
% 0.41/0.60  thf('171', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.41/0.60      inference('clc', [status(thm)], ['165', '170'])).
% 0.41/0.60  thf('172', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('174', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['147', '148', '171', '172', '173'])).
% 0.41/0.60  thf('175', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.41/0.60          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['140', '174'])).
% 0.41/0.60  thf('176', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['116', '117'])).
% 0.41/0.60  thf('177', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v3_pre_topc @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['175', '176'])).
% 0.41/0.60  thf('178', plain,
% 0.41/0.60      ((v3_pre_topc @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.60        sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['130', '177'])).
% 0.41/0.60  thf('179', plain, ($false), inference('demod', [status(thm)], ['129', '178'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
