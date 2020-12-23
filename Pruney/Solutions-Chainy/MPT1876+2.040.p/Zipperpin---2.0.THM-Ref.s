%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MTcNC1nSsJ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:01 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 331 expanded)
%              Number of leaves         :   38 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          : 1145 (3647 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( X27
        = ( u1_struct_0 @ ( sk_C_1 @ X27 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ~ ( v7_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('16',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( m1_pre_topc @ ( sk_C_1 @ X27 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ( v7_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
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
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('64',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('67',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,
    ( ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','61','68'])).

thf('70',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('73',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('74',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('79',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('93',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('99',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('105',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('106',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('111',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('112',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['112','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['94','119'])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','122'])).

thf('124',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('125',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','71','72','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MTcNC1nSsJ
% 0.13/0.38  % Computer   : n008.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 10:53:00 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.39  % Python version: Python 3.6.8
% 0.13/0.39  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 314 iterations in 0.218s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.72  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.51/0.72  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.72  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.51/0.72  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.51/0.72  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.51/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.72  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.51/0.72  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.51/0.72  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.51/0.72  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.51/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.72  thf(t44_tex_2, conjecture,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.51/0.72         ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.51/0.72             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.72           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i]:
% 0.51/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.72            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72          ( ![B:$i]:
% 0.51/0.72            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.51/0.72                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.72              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.51/0.72  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.72      inference('split', [status(esa)], ['0'])).
% 0.51/0.72  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('3', plain,
% 0.51/0.72      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['2'])).
% 0.51/0.72  thf('4', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t34_tex_2, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.51/0.72             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.72           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.51/0.72                ( ![C:$i]:
% 0.51/0.72                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.51/0.72                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.72                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('5', plain,
% 0.51/0.72      (![X27 : $i, X28 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X27)
% 0.51/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.51/0.72          | ~ (v2_tex_2 @ X27 @ X28)
% 0.51/0.72          | ((X27) = (u1_struct_0 @ (sk_C_1 @ X27 @ X28)))
% 0.51/0.72          | ~ (l1_pre_topc @ X28)
% 0.51/0.72          | ~ (v2_pre_topc @ X28)
% 0.51/0.72          | (v2_struct_0 @ X28))),
% 0.51/0.72      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.51/0.72  thf('6', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.72  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('9', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.51/0.72  thf('10', plain,
% 0.51/0.72      ((((v1_xboole_0 @ sk_B_1)
% 0.51/0.72         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.51/0.72         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['3', '9'])).
% 0.51/0.72  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('12', plain,
% 0.51/0.72      ((((v2_struct_0 @ sk_A)
% 0.51/0.72         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['10', '11'])).
% 0.51/0.72  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('14', plain,
% 0.51/0.72      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['12', '13'])).
% 0.51/0.72  thf(fc7_struct_0, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.72       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.51/0.72  thf('15', plain,
% 0.51/0.72      (![X17 : $i]:
% 0.51/0.72         ((v1_zfmisc_1 @ (u1_struct_0 @ X17))
% 0.51/0.72          | ~ (l1_struct_0 @ X17)
% 0.51/0.72          | ~ (v7_struct_0 @ X17))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.51/0.72  thf('16', plain,
% 0.51/0.72      ((((v1_zfmisc_1 @ sk_B_1)
% 0.51/0.72         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.51/0.72  thf('17', plain,
% 0.51/0.72      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['2'])).
% 0.51/0.72  thf('18', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('19', plain,
% 0.51/0.72      (![X27 : $i, X28 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X27)
% 0.51/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.51/0.72          | ~ (v2_tex_2 @ X27 @ X28)
% 0.51/0.72          | (m1_pre_topc @ (sk_C_1 @ X27 @ X28) @ X28)
% 0.51/0.72          | ~ (l1_pre_topc @ X28)
% 0.51/0.72          | ~ (v2_pre_topc @ X28)
% 0.51/0.72          | (v2_struct_0 @ X28))),
% 0.51/0.72      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.51/0.72  thf('20', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.72  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('23', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.51/0.72  thf('24', plain,
% 0.51/0.72      ((((v1_xboole_0 @ sk_B_1)
% 0.51/0.72         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.51/0.72         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['17', '23'])).
% 0.51/0.72  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('26', plain,
% 0.51/0.72      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['24', '25'])).
% 0.51/0.72  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('28', plain,
% 0.51/0.72      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['26', '27'])).
% 0.51/0.72  thf(cc32_tex_2, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.51/0.72         ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_pre_topc @ B @ A ) =>
% 0.51/0.72           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.51/0.72             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.51/0.72  thf('29', plain,
% 0.51/0.72      (![X23 : $i, X24 : $i]:
% 0.51/0.72         (~ (m1_pre_topc @ X23 @ X24)
% 0.51/0.72          | ~ (v1_tdlat_3 @ X23)
% 0.51/0.72          | (v7_struct_0 @ X23)
% 0.51/0.72          | (v2_struct_0 @ X23)
% 0.51/0.72          | ~ (l1_pre_topc @ X24)
% 0.51/0.72          | ~ (v2_tdlat_3 @ X24)
% 0.51/0.72          | ~ (v2_pre_topc @ X24)
% 0.51/0.72          | (v2_struct_0 @ X24))),
% 0.51/0.72      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.51/0.72  thf('30', plain,
% 0.51/0.72      ((((v2_struct_0 @ sk_A)
% 0.51/0.72         | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72         | ~ (v2_tdlat_3 @ sk_A)
% 0.51/0.72         | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.72  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('32', plain, ((v2_tdlat_3 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('34', plain,
% 0.51/0.72      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['2'])).
% 0.51/0.72  thf('35', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('36', plain,
% 0.51/0.72      (![X27 : $i, X28 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X27)
% 0.51/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.51/0.72          | ~ (v2_tex_2 @ X27 @ X28)
% 0.51/0.72          | (v1_tdlat_3 @ (sk_C_1 @ X27 @ X28))
% 0.51/0.72          | ~ (l1_pre_topc @ X28)
% 0.51/0.72          | ~ (v2_pre_topc @ X28)
% 0.51/0.72          | (v2_struct_0 @ X28))),
% 0.51/0.72      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.51/0.72  thf('37', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.51/0.72  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('40', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.51/0.72  thf('41', plain,
% 0.51/0.72      ((((v1_xboole_0 @ sk_B_1)
% 0.51/0.72         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['34', '40'])).
% 0.51/0.72  thf('42', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('43', plain,
% 0.51/0.72      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['41', '42'])).
% 0.51/0.72  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('45', plain,
% 0.51/0.72      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['43', '44'])).
% 0.51/0.72  thf('46', plain,
% 0.51/0.72      ((((v2_struct_0 @ sk_A)
% 0.51/0.72         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['30', '31', '32', '33', '45'])).
% 0.51/0.72  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('48', plain,
% 0.51/0.72      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['46', '47'])).
% 0.51/0.72  thf('49', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('50', plain,
% 0.51/0.72      (![X27 : $i, X28 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X27)
% 0.51/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.51/0.72          | ~ (v2_tex_2 @ X27 @ X28)
% 0.51/0.72          | ~ (v2_struct_0 @ (sk_C_1 @ X27 @ X28))
% 0.51/0.72          | ~ (l1_pre_topc @ X28)
% 0.51/0.72          | ~ (v2_pre_topc @ X28)
% 0.51/0.72          | (v2_struct_0 @ X28))),
% 0.51/0.72      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.51/0.72  thf('51', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.72  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('54', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.51/0.72  thf('55', plain,
% 0.51/0.72      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | (v1_xboole_0 @ sk_B_1)
% 0.51/0.72         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['48', '54'])).
% 0.51/0.72  thf('56', plain,
% 0.51/0.72      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['2'])).
% 0.51/0.72  thf('57', plain,
% 0.51/0.72      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.51/0.72         | (v1_xboole_0 @ sk_B_1)
% 0.51/0.72         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['55', '56'])).
% 0.51/0.72  thf('58', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('59', plain,
% 0.51/0.72      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['57', '58'])).
% 0.51/0.72  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('61', plain,
% 0.51/0.72      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['59', '60'])).
% 0.51/0.72  thf('62', plain,
% 0.51/0.72      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('clc', [status(thm)], ['26', '27'])).
% 0.51/0.72  thf(dt_m1_pre_topc, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( l1_pre_topc @ A ) =>
% 0.51/0.72       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.51/0.72  thf('63', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (m1_pre_topc @ X15 @ X16)
% 0.51/0.72          | (l1_pre_topc @ X15)
% 0.51/0.72          | ~ (l1_pre_topc @ X16))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.51/0.72  thf('64', plain,
% 0.51/0.72      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.51/0.72  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('66', plain,
% 0.51/0.72      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['64', '65'])).
% 0.51/0.72  thf(dt_l1_pre_topc, axiom,
% 0.51/0.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.51/0.72  thf('67', plain,
% 0.51/0.72      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.72  thf('68', plain,
% 0.51/0.72      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.51/0.72         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['66', '67'])).
% 0.51/0.72  thf('69', plain,
% 0.51/0.72      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['16', '61', '68'])).
% 0.51/0.72  thf('70', plain,
% 0.51/0.72      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.51/0.72      inference('split', [status(esa)], ['0'])).
% 0.51/0.72  thf('71', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['69', '70'])).
% 0.51/0.72  thf('72', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.72      inference('split', [status(esa)], ['2'])).
% 0.51/0.72  thf('73', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.51/0.72      inference('split', [status(esa)], ['2'])).
% 0.51/0.72  thf(d1_xboole_0, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.72  thf('74', plain,
% 0.51/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.51/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.72  thf(d2_subset_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ( v1_xboole_0 @ A ) =>
% 0.51/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.51/0.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.72  thf('75', plain,
% 0.51/0.72      (![X8 : $i, X9 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X8 @ X9)
% 0.51/0.72          | (m1_subset_1 @ X8 @ X9)
% 0.51/0.72          | (v1_xboole_0 @ X9))),
% 0.51/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.72  thf('76', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.72  thf('77', plain,
% 0.51/0.72      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.51/0.72      inference('clc', [status(thm)], ['75', '76'])).
% 0.51/0.72  thf('78', plain,
% 0.51/0.72      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['74', '77'])).
% 0.51/0.72  thf(redefinition_k6_domain_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.51/0.72       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.51/0.72  thf('79', plain,
% 0.51/0.72      (![X20 : $i, X21 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X20)
% 0.51/0.72          | ~ (m1_subset_1 @ X21 @ X20)
% 0.51/0.72          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.51/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.51/0.72  thf('80', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X0)
% 0.51/0.72          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.51/0.72          | (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['78', '79'])).
% 0.51/0.72  thf('81', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.51/0.72          | (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['80'])).
% 0.51/0.72  thf('82', plain,
% 0.51/0.72      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['74', '77'])).
% 0.51/0.72  thf(dt_k6_domain_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.51/0.72       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.72  thf('83', plain,
% 0.51/0.72      (![X18 : $i, X19 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X18)
% 0.51/0.72          | ~ (m1_subset_1 @ X19 @ X18)
% 0.51/0.72          | (m1_subset_1 @ (k6_domain_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.51/0.72  thf('84', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X0)
% 0.51/0.72          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.51/0.72             (k1_zfmisc_1 @ X0))
% 0.51/0.72          | (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['82', '83'])).
% 0.51/0.72  thf('85', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.51/0.72          | (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['84'])).
% 0.51/0.72  thf('86', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.51/0.72          | (v1_xboole_0 @ X0)
% 0.51/0.72          | (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('sup+', [status(thm)], ['81', '85'])).
% 0.51/0.72  thf('87', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X0)
% 0.51/0.72          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.51/0.72      inference('simplify', [status(thm)], ['86'])).
% 0.51/0.72  thf(t3_subset, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.72  thf('88', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i]:
% 0.51/0.72         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.72  thf('89', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['87', '88'])).
% 0.51/0.72  thf(t1_tex_2, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.51/0.72           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.51/0.72  thf('90', plain,
% 0.51/0.72      (![X25 : $i, X26 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X25)
% 0.51/0.72          | ~ (v1_zfmisc_1 @ X25)
% 0.51/0.72          | ((X26) = (X25))
% 0.51/0.72          | ~ (r1_tarski @ X26 @ X25)
% 0.51/0.72          | (v1_xboole_0 @ X26))),
% 0.51/0.72      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.51/0.72  thf('91', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X0)
% 0.51/0.72          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.51/0.72          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.51/0.72          | ~ (v1_zfmisc_1 @ X0)
% 0.51/0.72          | (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['89', '90'])).
% 0.51/0.72  thf('92', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (v1_zfmisc_1 @ X0)
% 0.51/0.72          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.51/0.72          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.51/0.72          | (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['91'])).
% 0.51/0.72  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.51/0.72  thf('93', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.51/0.72  thf('94', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X0)
% 0.51/0.72          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.51/0.72          | ~ (v1_zfmisc_1 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['92', '93'])).
% 0.51/0.72  thf('95', plain,
% 0.51/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.51/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.72  thf('96', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('97', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i]:
% 0.51/0.72         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.72  thf('98', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['96', '97'])).
% 0.51/0.72  thf(d3_tarski, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.72  thf('99', plain,
% 0.51/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X3 @ X4)
% 0.51/0.72          | (r2_hidden @ X3 @ X5)
% 0.51/0.72          | ~ (r1_tarski @ X4 @ X5))),
% 0.51/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.72  thf('100', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['98', '99'])).
% 0.51/0.72  thf('101', plain,
% 0.51/0.72      (((v1_xboole_0 @ sk_B_1)
% 0.51/0.72        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['95', '100'])).
% 0.51/0.72  thf('102', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('103', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('clc', [status(thm)], ['101', '102'])).
% 0.51/0.72  thf('104', plain,
% 0.51/0.72      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.51/0.72      inference('clc', [status(thm)], ['75', '76'])).
% 0.51/0.72  thf('105', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['103', '104'])).
% 0.51/0.72  thf(t36_tex_2, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.51/0.72  thf('106', plain,
% 0.51/0.72      (![X29 : $i, X30 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.51/0.72          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.51/0.72          | ~ (l1_pre_topc @ X30)
% 0.51/0.72          | ~ (v2_pre_topc @ X30)
% 0.51/0.72          | (v2_struct_0 @ X30))),
% 0.51/0.72      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.51/0.72  thf('107', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.51/0.72           sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['105', '106'])).
% 0.51/0.72  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('110', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['103', '104'])).
% 0.51/0.72  thf('111', plain,
% 0.51/0.72      (![X20 : $i, X21 : $i]:
% 0.51/0.72         ((v1_xboole_0 @ X20)
% 0.51/0.72          | ~ (m1_subset_1 @ X21 @ X20)
% 0.51/0.72          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.51/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.51/0.72  thf('112', plain,
% 0.51/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.51/0.72          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.51/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['110', '111'])).
% 0.51/0.72  thf('113', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('clc', [status(thm)], ['101', '102'])).
% 0.51/0.72  thf('114', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.72  thf('115', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['113', '114'])).
% 0.51/0.72  thf('116', plain,
% 0.51/0.72      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.51/0.72         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.51/0.72      inference('clc', [status(thm)], ['112', '115'])).
% 0.51/0.72  thf('117', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.51/0.72      inference('demod', [status(thm)], ['107', '108', '109', '116'])).
% 0.51/0.72  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('119', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.51/0.72      inference('clc', [status(thm)], ['117', '118'])).
% 0.51/0.72  thf('120', plain,
% 0.51/0.72      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.72        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.51/0.72        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.72      inference('sup+', [status(thm)], ['94', '119'])).
% 0.51/0.72  thf('121', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('122', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.72      inference('clc', [status(thm)], ['120', '121'])).
% 0.51/0.72  thf('123', plain,
% 0.51/0.72      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['73', '122'])).
% 0.51/0.72  thf('124', plain,
% 0.51/0.72      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['0'])).
% 0.51/0.72  thf('125', plain,
% 0.51/0.72      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['123', '124'])).
% 0.51/0.72  thf('126', plain, ($false),
% 0.51/0.72      inference('sat_resolution*', [status(thm)], ['1', '71', '72', '125'])).
% 0.51/0.72  
% 0.51/0.72  % SZS output end Refutation
% 0.51/0.72  
% 0.51/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
