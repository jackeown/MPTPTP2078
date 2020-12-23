%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4YFzx1ooxz

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 374 expanded)
%              Number of leaves         :   24 ( 112 expanded)
%              Depth                    :   28
%              Number of atoms          : 1057 (4850 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t50_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v3_tex_2 @ B @ A )
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
           => ( ( v3_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tex_2])).

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_tex_2 @ X9 @ X10 )
      | ( v2_tex_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tex_2,axiom,(
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

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( v1_zfmisc_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_zfmisc_1 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ sk_B_1 ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_zfmisc_1 @ X14 )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X10 )
      | ( v2_tex_2 @ ( sk_C @ X9 @ X10 ) @ X10 )
      | ( v3_tex_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_tex_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( v1_zfmisc_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('54',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X10 )
      | ( r1_tarski @ X9 @ ( sk_C @ X9 @ X10 ) )
      | ( v3_tex_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( v3_tex_2 @ sk_B_1 @ sk_A )
        | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( v3_tex_2 @ sk_B_1 @ sk_A )
        | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','73'])).

thf('75',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( v1_zfmisc_1 @ X12 )
      | ( X13 = X12 )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('77',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( v3_tex_2 @ sk_B_1 @ sk_A )
        | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v3_tex_2 @ sk_B_1 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 )
        | ( sk_B_1
          = ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( sk_B_1
          = ( sk_C @ sk_B_1 @ sk_A ) )
        | ( v1_xboole_0 @ sk_B_1 )
        | ( v3_tex_2 @ sk_B_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','82'])).

thf('84',plain,
    ( ( ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( sk_B_1
      = ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X10 )
      | ( X9
       != ( sk_C @ X9 @ X10 ) )
      | ( v3_tex_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( sk_B_1
       != ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4YFzx1ooxz
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 71 iterations in 0.037s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.49  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(t50_tex_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.49         ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.20/0.49  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d7_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.49             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.49               ( ![C:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.49                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.49          | ~ (v3_tex_2 @ X9 @ X10)
% 0.20/0.49          | (v2_tex_2 @ X9 @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t44_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.49         ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X14)
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.49          | ~ (v2_tex_2 @ X14 @ X15)
% 0.20/0.49          | (v1_zfmisc_1 @ X14)
% 0.20/0.49          | ~ (l1_pre_topc @ X15)
% 0.20/0.49          | ~ (v2_tdlat_3 @ X15)
% 0.20/0.49          | ~ (v2_pre_topc @ X15)
% 0.20/0.49          | (v2_struct_0 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.49  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.20/0.49         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('27', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X14)
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X14)
% 0.20/0.49          | (v2_tex_2 @ X14 @ X15)
% 0.20/0.49          | ~ (l1_pre_topc @ X15)
% 0.20/0.49          | ~ (v2_tdlat_3 @ X15)
% 0.20/0.49          | ~ (v2_pre_topc @ X15)
% 0.20/0.49          | (v2_struct_0 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '34'])).
% 0.20/0.49  thf('36', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.49          | ~ (v2_tex_2 @ X9 @ X10)
% 0.20/0.49          | (v2_tex_2 @ (sk_C @ X9 @ X10) @ X10)
% 0.20/0.49          | (v3_tex_2 @ X9 @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.49          | ~ (v2_tex_2 @ X9 @ X10)
% 0.20/0.49          | (m1_subset_1 @ (sk_C @ X9 @ X10) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.49          | (v3_tex_2 @ X9 @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.49          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['46', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X14)
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.49          | ~ (v2_tex_2 @ X14 @ X15)
% 0.20/0.49          | (v1_zfmisc_1 @ X14)
% 0.20/0.49          | ~ (l1_pre_topc @ X15)
% 0.20/0.49          | ~ (v2_tdlat_3 @ X15)
% 0.20/0.49          | ~ (v2_pre_topc @ X15)
% 0.20/0.49          | (v2_struct_0 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)
% 0.20/0.49         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49         | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.49         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | ~ (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.49         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)
% 0.20/0.49         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | ~ (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.49         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v2_struct_0 @ sk_A)
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((((v2_struct_0 @ sk_A)
% 0.20/0.49         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.49          | ~ (v2_tex_2 @ X9 @ X10)
% 0.20/0.49          | (r1_tarski @ X9 @ (sk_C @ X9 @ X10))
% 0.20/0.49          | (v3_tex_2 @ X9 @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      ((((r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['61', '66'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A)))))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.49  thf(t5_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.49          | ~ (v1_xboole_0 @ X8)
% 0.20/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49           | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49           | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49           | (v2_struct_0 @ sk_A)
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.49           | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['60', '71'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.49           | (v2_struct_0 @ sk_A)
% 0.20/0.49           | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49           | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['72'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '73'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      ((((r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['61', '66'])).
% 0.20/0.49  thf(t1_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X12)
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X12)
% 0.20/0.49          | ((X13) = (X12))
% 0.20/0.49          | ~ (r1_tarski @ X13 @ X12)
% 0.20/0.49          | (v1_xboole_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      ((((v2_struct_0 @ sk_A)
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['74', '77'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      (((((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['78'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49           | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((v2_struct_0 @ sk_A)
% 0.20/0.49           | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49           | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49           | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.49           | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.49  thf('82', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.49           | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49           | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49           | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49           | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | (v2_struct_0 @ sk_A)
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '82'])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (((((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)
% 0.20/0.49         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.49  thf('85', plain,
% 0.20/0.49      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.49         | (v2_struct_0 @ sk_A)
% 0.20/0.49         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.49         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.49  thf('87', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      (((((sk_B_1) = (sk_C @ sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.49  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      ((((sk_B_1) = (sk_C @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('92', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('93', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.49          | ~ (v2_tex_2 @ X9 @ X10)
% 0.20/0.49          | ((X9) != (sk_C @ X9 @ X10))
% 0.20/0.49          | (v3_tex_2 @ X9 @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | ((sk_B_1) != (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.49  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('96', plain,
% 0.20/0.49      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.49        | ((sk_B_1) != (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.49  thf('97', plain,
% 0.20/0.49      (((((sk_B_1) != (sk_C @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['91', '96'])).
% 0.20/0.49  thf('98', plain,
% 0.20/0.49      (((((sk_B_1) != (sk_B_1)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['90', '97'])).
% 0.20/0.49  thf('99', plain,
% 0.20/0.49      (((v3_tex_2 @ sk_B_1 @ sk_A))
% 0.20/0.49         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['98'])).
% 0.20/0.49  thf('100', plain,
% 0.20/0.49      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('101', plain,
% 0.20/0.49      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.49  thf('102', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '101'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
