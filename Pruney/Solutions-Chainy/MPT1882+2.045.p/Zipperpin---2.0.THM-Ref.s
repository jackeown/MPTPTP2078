%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJ2K6D4VWJ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 269 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   22
%              Number of atoms          :  992 (3363 expanded)
%              Number of equality atoms :   34 (  37 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_tex_2 @ X12 @ X13 )
      | ( v2_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( v1_zfmisc_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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

thf('25',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_zfmisc_1 @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( C != k1_xboole_0 )
                    & ( v3_pre_topc @ C @ A )
                    & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( sk_C @ X9 @ X10 ) @ X10 )
      | ( v1_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(t20_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v2_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( v3_pre_topc @ B @ A )
                & ( B != k1_xboole_0 )
                & ( B
                 != ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_tdlat_3 @ X15 )
      | ( X16
        = ( u1_struct_0 @ X15 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t20_tdlat_3])).

thf('51',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','55'])).

thf('57',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( sk_C @ X9 @ X10 )
       != k1_xboole_0 )
      | ( v1_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('60',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( ( sk_C @ sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_xboole_0 @ X9 @ ( sk_C @ X9 @ X10 ) )
      | ( v1_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('79',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( r1_xboole_0 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( r1_xboole_0 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('84',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( ( k4_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
        = sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['76','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('93',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('95',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJ2K6D4VWJ
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:47:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 191 iterations in 0.097s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.56  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(t50_tex_2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.56         ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.56            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.21/0.56  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d7_tex_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.56             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.56               ( ![C:$i]:
% 0.21/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.56                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.56          | ~ (v3_tex_2 @ X12 @ X13)
% 0.21/0.56          | (v2_tex_2 @ X12 @ X13)
% 0.21/0.56          | ~ (l1_pre_topc @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t44_tex_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.56         ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X17)
% 0.21/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | ~ (v2_tex_2 @ X17 @ X18)
% 0.21/0.56          | (v1_zfmisc_1 @ X17)
% 0.21/0.56          | ~ (l1_pre_topc @ X18)
% 0.21/0.56          | ~ (v2_tdlat_3 @ X18)
% 0.21/0.56          | ~ (v2_pre_topc @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.56  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.21/0.56         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('25', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X17)
% 0.21/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | ~ (v1_zfmisc_1 @ X17)
% 0.21/0.56          | (v2_tex_2 @ X17 @ X18)
% 0.21/0.56          | ~ (l1_pre_topc @ X18)
% 0.21/0.56          | ~ (v2_tdlat_3 @ X18)
% 0.21/0.56          | ~ (v2_pre_topc @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.56         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '32'])).
% 0.21/0.56  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t80_tops_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.56             ( ![C:$i]:
% 0.21/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56                 ( ~( ( ( C ) != ( k1_xboole_0 ) ) & ( v3_pre_topc @ C @ A ) & 
% 0.21/0.56                      ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.56          | (v3_pre_topc @ (sk_C @ X9 @ X10) @ X10)
% 0.21/0.56          | (v1_tops_1 @ X9 @ X10)
% 0.21/0.56          | ~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v2_pre_topc @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.56          | (m1_subset_1 @ (sk_C @ X9 @ X10) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.56          | (v1_tops_1 @ X9 @ X10)
% 0.21/0.56          | ~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v2_pre_topc @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.56  thf(t20_tdlat_3, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ( v2_tdlat_3 @ A ) <=>
% 0.21/0.56         ( ![B:$i]:
% 0.21/0.56           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56             ( ~( ( v3_pre_topc @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56                  ( ( B ) != ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (v2_tdlat_3 @ X15)
% 0.21/0.56          | ((X16) = (u1_struct_0 @ X15))
% 0.21/0.56          | ((X16) = (k1_xboole_0))
% 0.21/0.56          | ~ (v3_pre_topc @ X16 @ X15)
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t20_tdlat_3])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.56        | ~ (v2_tdlat_3 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      ((((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.56          | ((sk_C @ X9 @ X10) != (k1_xboole_0))
% 0.21/0.56          | (v1_tops_1 @ X9 @ X10)
% 0.21/0.56          | ~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v2_pre_topc @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.56  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A) | ((sk_C @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('clc', [status(thm)], ['57', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t48_tex_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.56             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.56          | (v3_tex_2 @ X19 @ X20)
% 0.21/0.56          | ~ (v2_tex_2 @ X19 @ X20)
% 0.21/0.56          | ~ (v1_tops_1 @ X19 @ X20)
% 0.21/0.56          | ~ (l1_pre_topc @ X20)
% 0.21/0.56          | ~ (v2_pre_topc @ X20)
% 0.21/0.56          | (v2_struct_0 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.56  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['64', '70'])).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A)
% 0.21/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56         | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.21/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['37', '71'])).
% 0.21/0.56  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('clc', [status(thm)], ['72', '73'])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.56          | (r1_xboole_0 @ X9 @ (sk_C @ X9 @ X10))
% 0.21/0.56          | (v1_tops_1 @ X9 @ X10)
% 0.21/0.56          | ~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v2_pre_topc @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (r1_xboole_0 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.56  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (r1_xboole_0 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.21/0.56  thf(t83_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ((k4_xboole_0 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)) = (sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      (((((k4_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B_1))
% 0.21/0.56         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['76', '84'])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t3_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('87', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i]:
% 0.21/0.56         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('88', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.56  thf(l32_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('89', plain,
% 0.21/0.56      (![X0 : $i, X2 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.56  thf('90', plain,
% 0.21/0.56      (((k4_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.56  thf('91', plain,
% 0.21/0.56      (((((sk_B_1) = (k1_xboole_0)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['85', '90'])).
% 0.21/0.56  thf('92', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.56  thf('93', plain,
% 0.21/0.56      (((((sk_B_1) = (k1_xboole_0))
% 0.21/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56         | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.56  thf('94', plain,
% 0.21/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('95', plain,
% 0.21/0.56      (((((sk_B_1) = (k1_xboole_0))
% 0.21/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.56         | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.56  thf('96', plain,
% 0.21/0.56      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.56  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('99', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0)))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.56  thf('100', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('101', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.21/0.56         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.56  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.56  thf('104', plain, ($false),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '103'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
