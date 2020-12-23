%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DgiRUgUA1W

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:01 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 307 expanded)
%              Number of leaves         :   38 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          : 1041 (3442 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( X28
        = ( u1_struct_0 @ ( sk_C_1 @ X28 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X20: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( v7_struct_0 @ X20 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( m1_pre_topc @ ( sk_C_1 @ X28 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ( v7_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X28 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X28 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('75',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( X27 = X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('80',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('86',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['88','89'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( m1_subset_1 @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('95',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('100',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('101',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['101','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['81','108'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','111'])).

thf('113',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','71','72','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DgiRUgUA1W
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:18:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.91  % Solved by: fo/fo7.sh
% 0.71/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.91  % done 838 iterations in 0.457s
% 0.71/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.91  % SZS output start Refutation
% 0.71/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.91  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.71/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.71/0.91  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.71/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.91  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.71/0.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.71/0.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.71/0.91  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.71/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.71/0.91  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.71/0.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.71/0.91  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.71/0.91  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.71/0.91  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.71/0.91  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.71/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.91  thf(t44_tex_2, conjecture,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.71/0.91         ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.71/0.91             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.91           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.71/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.91    (~( ![A:$i]:
% 0.71/0.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.71/0.91            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91          ( ![B:$i]:
% 0.71/0.91            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.71/0.91                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.91              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.71/0.91    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.71/0.91  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('1', plain,
% 0.71/0.91      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.71/0.91      inference('split', [status(esa)], ['0'])).
% 0.71/0.91  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('3', plain,
% 0.71/0.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['2'])).
% 0.71/0.91  thf('4', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t34_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.71/0.91             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.91           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.71/0.91                ( ![C:$i]:
% 0.71/0.91                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.71/0.91                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.71/0.91                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.71/0.91  thf('5', plain,
% 0.71/0.91      (![X28 : $i, X29 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X28)
% 0.71/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.71/0.91          | ~ (v2_tex_2 @ X28 @ X29)
% 0.71/0.91          | ((X28) = (u1_struct_0 @ (sk_C_1 @ X28 @ X29)))
% 0.71/0.91          | ~ (l1_pre_topc @ X29)
% 0.71/0.91          | ~ (v2_pre_topc @ X29)
% 0.71/0.91          | (v2_struct_0 @ X29))),
% 0.71/0.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.71/0.91  thf('6', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.71/0.91  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('9', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.71/0.91  thf('10', plain,
% 0.71/0.91      ((((v1_xboole_0 @ sk_B_1)
% 0.71/0.91         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.71/0.91         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['3', '9'])).
% 0.71/0.91  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('12', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['10', '11'])).
% 0.71/0.91  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('14', plain,
% 0.71/0.91      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['12', '13'])).
% 0.71/0.91  thf(fc7_struct_0, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.71/0.91       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.71/0.91  thf('15', plain,
% 0.71/0.91      (![X20 : $i]:
% 0.71/0.91         ((v1_zfmisc_1 @ (u1_struct_0 @ X20))
% 0.71/0.91          | ~ (l1_struct_0 @ X20)
% 0.71/0.91          | ~ (v7_struct_0 @ X20))),
% 0.71/0.91      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.71/0.91  thf('16', plain,
% 0.71/0.91      ((((v1_zfmisc_1 @ sk_B_1)
% 0.71/0.91         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['14', '15'])).
% 0.71/0.91  thf('17', plain,
% 0.71/0.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['2'])).
% 0.71/0.91  thf('18', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('19', plain,
% 0.71/0.91      (![X28 : $i, X29 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X28)
% 0.71/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.71/0.91          | ~ (v2_tex_2 @ X28 @ X29)
% 0.71/0.91          | (m1_pre_topc @ (sk_C_1 @ X28 @ X29) @ X29)
% 0.71/0.91          | ~ (l1_pre_topc @ X29)
% 0.71/0.91          | ~ (v2_pre_topc @ X29)
% 0.71/0.91          | (v2_struct_0 @ X29))),
% 0.71/0.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.71/0.91  thf('20', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.71/0.91  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('23', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.71/0.91  thf('24', plain,
% 0.71/0.91      ((((v1_xboole_0 @ sk_B_1)
% 0.71/0.91         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.71/0.91         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['17', '23'])).
% 0.71/0.91  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('26', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['24', '25'])).
% 0.71/0.91  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('28', plain,
% 0.71/0.91      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['26', '27'])).
% 0.71/0.91  thf(cc32_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.71/0.91         ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.71/0.91           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.71/0.91             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.71/0.91  thf('29', plain,
% 0.71/0.91      (![X24 : $i, X25 : $i]:
% 0.71/0.91         (~ (m1_pre_topc @ X24 @ X25)
% 0.71/0.91          | ~ (v1_tdlat_3 @ X24)
% 0.71/0.91          | (v7_struct_0 @ X24)
% 0.71/0.91          | (v2_struct_0 @ X24)
% 0.71/0.91          | ~ (l1_pre_topc @ X25)
% 0.71/0.91          | ~ (v2_tdlat_3 @ X25)
% 0.71/0.91          | ~ (v2_pre_topc @ X25)
% 0.71/0.91          | (v2_struct_0 @ X25))),
% 0.71/0.91      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.71/0.91  thf('30', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91         | ~ (v2_tdlat_3 @ sk_A)
% 0.71/0.91         | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['28', '29'])).
% 0.71/0.91  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('32', plain, ((v2_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('34', plain,
% 0.71/0.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['2'])).
% 0.71/0.91  thf('35', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('36', plain,
% 0.71/0.91      (![X28 : $i, X29 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X28)
% 0.71/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.71/0.91          | ~ (v2_tex_2 @ X28 @ X29)
% 0.71/0.91          | (v1_tdlat_3 @ (sk_C_1 @ X28 @ X29))
% 0.71/0.91          | ~ (l1_pre_topc @ X29)
% 0.71/0.91          | ~ (v2_pre_topc @ X29)
% 0.71/0.91          | (v2_struct_0 @ X29))),
% 0.71/0.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.71/0.91  thf('37', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.71/0.91  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('40', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.71/0.91  thf('41', plain,
% 0.71/0.91      ((((v1_xboole_0 @ sk_B_1)
% 0.71/0.91         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['34', '40'])).
% 0.71/0.91  thf('42', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('43', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['41', '42'])).
% 0.71/0.91  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('45', plain,
% 0.71/0.91      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['43', '44'])).
% 0.71/0.91  thf('46', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['30', '31', '32', '33', '45'])).
% 0.71/0.91  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('48', plain,
% 0.71/0.91      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['46', '47'])).
% 0.71/0.91  thf('49', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('50', plain,
% 0.71/0.91      (![X28 : $i, X29 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X28)
% 0.71/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.71/0.91          | ~ (v2_tex_2 @ X28 @ X29)
% 0.71/0.91          | ~ (v2_struct_0 @ (sk_C_1 @ X28 @ X29))
% 0.71/0.91          | ~ (l1_pre_topc @ X29)
% 0.71/0.91          | ~ (v2_pre_topc @ X29)
% 0.71/0.91          | (v2_struct_0 @ X29))),
% 0.71/0.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.71/0.91  thf('51', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('sup-', [status(thm)], ['49', '50'])).
% 0.71/0.91  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('54', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.71/0.91  thf('55', plain,
% 0.71/0.91      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | (v1_xboole_0 @ sk_B_1)
% 0.71/0.91         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['48', '54'])).
% 0.71/0.91  thf('56', plain,
% 0.71/0.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['2'])).
% 0.71/0.91  thf('57', plain,
% 0.71/0.91      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.71/0.91         | (v1_xboole_0 @ sk_B_1)
% 0.71/0.91         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['55', '56'])).
% 0.71/0.91  thf('58', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('59', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['57', '58'])).
% 0.71/0.91  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('61', plain,
% 0.71/0.91      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['59', '60'])).
% 0.71/0.91  thf('62', plain,
% 0.71/0.91      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['26', '27'])).
% 0.71/0.91  thf(dt_m1_pre_topc, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( l1_pre_topc @ A ) =>
% 0.71/0.91       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.71/0.91  thf('63', plain,
% 0.71/0.91      (![X18 : $i, X19 : $i]:
% 0.71/0.91         (~ (m1_pre_topc @ X18 @ X19)
% 0.71/0.91          | (l1_pre_topc @ X18)
% 0.71/0.91          | ~ (l1_pre_topc @ X19))),
% 0.71/0.91      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.71/0.91  thf('64', plain,
% 0.71/0.91      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['62', '63'])).
% 0.71/0.91  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('66', plain,
% 0.71/0.91      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['64', '65'])).
% 0.71/0.91  thf(dt_l1_pre_topc, axiom,
% 0.71/0.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.71/0.91  thf('67', plain,
% 0.71/0.91      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.71/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.71/0.91  thf('68', plain,
% 0.71/0.91      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.71/0.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['66', '67'])).
% 0.71/0.91  thf('69', plain,
% 0.71/0.91      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['16', '61', '68'])).
% 0.71/0.91  thf('70', plain,
% 0.71/0.91      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.71/0.91      inference('split', [status(esa)], ['0'])).
% 0.71/0.91  thf('71', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['69', '70'])).
% 0.71/0.91  thf('72', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.71/0.91      inference('split', [status(esa)], ['2'])).
% 0.71/0.91  thf('73', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.71/0.91      inference('split', [status(esa)], ['2'])).
% 0.71/0.91  thf(d1_xboole_0, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.71/0.91  thf('74', plain,
% 0.71/0.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.71/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.91  thf(l1_zfmisc_1, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.71/0.91  thf('75', plain,
% 0.71/0.91      (![X8 : $i, X10 : $i]:
% 0.71/0.91         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.71/0.91      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.71/0.91  thf('76', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.71/0.91  thf(t1_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.71/0.91           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.71/0.91  thf('77', plain,
% 0.71/0.91      (![X26 : $i, X27 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X26)
% 0.71/0.91          | ~ (v1_zfmisc_1 @ X26)
% 0.71/0.91          | ((X27) = (X26))
% 0.71/0.91          | ~ (r1_tarski @ X27 @ X26)
% 0.71/0.91          | (v1_xboole_0 @ X27))),
% 0.71/0.91      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.71/0.91  thf('78', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X0)
% 0.71/0.91          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.71/0.91          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.71/0.91          | ~ (v1_zfmisc_1 @ X0)
% 0.71/0.91          | (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['76', '77'])).
% 0.71/0.91  thf('79', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v1_zfmisc_1 @ X0)
% 0.71/0.91          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.71/0.91          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.71/0.91          | (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('simplify', [status(thm)], ['78'])).
% 0.71/0.91  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.71/0.91  thf('80', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.71/0.91      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.71/0.91  thf('81', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X0)
% 0.71/0.91          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.71/0.91          | ~ (v1_zfmisc_1 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['79', '80'])).
% 0.71/0.91  thf('82', plain,
% 0.71/0.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.71/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.91  thf('83', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t3_subset, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.91  thf('84', plain,
% 0.71/0.91      (![X14 : $i, X15 : $i]:
% 0.71/0.91         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('85', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.91  thf(d3_tarski, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.71/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.71/0.91  thf('86', plain,
% 0.71/0.91      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X3 @ X4)
% 0.71/0.91          | (r2_hidden @ X3 @ X5)
% 0.71/0.91          | ~ (r1_tarski @ X4 @ X5))),
% 0.71/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.91  thf('87', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.71/0.91      inference('sup-', [status(thm)], ['85', '86'])).
% 0.71/0.91  thf('88', plain,
% 0.71/0.91      (((v1_xboole_0 @ sk_B_1)
% 0.71/0.91        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['82', '87'])).
% 0.71/0.91  thf('89', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('90', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.71/0.91      inference('clc', [status(thm)], ['88', '89'])).
% 0.71/0.91  thf(d2_subset_1, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( ( v1_xboole_0 @ A ) =>
% 0.71/0.91         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.71/0.91       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.71/0.91         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.71/0.91  thf('91', plain,
% 0.71/0.91      (![X11 : $i, X12 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X11 @ X12)
% 0.71/0.91          | (m1_subset_1 @ X11 @ X12)
% 0.71/0.91          | (v1_xboole_0 @ X12))),
% 0.71/0.91      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.71/0.91  thf('92', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.91  thf('93', plain,
% 0.71/0.91      (![X11 : $i, X12 : $i]:
% 0.71/0.91         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.71/0.91      inference('clc', [status(thm)], ['91', '92'])).
% 0.71/0.91  thf('94', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['90', '93'])).
% 0.71/0.91  thf(t36_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.91           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.71/0.91  thf('95', plain,
% 0.71/0.91      (![X30 : $i, X31 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.71/0.91          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.71/0.91          | ~ (l1_pre_topc @ X31)
% 0.71/0.91          | ~ (v2_pre_topc @ X31)
% 0.71/0.91          | (v2_struct_0 @ X31))),
% 0.71/0.91      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.71/0.91  thf('96', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.71/0.91           sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['94', '95'])).
% 0.71/0.91  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('99', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['90', '93'])).
% 0.71/0.91  thf(redefinition_k6_domain_1, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.71/0.91       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.71/0.91  thf('100', plain,
% 0.71/0.91      (![X21 : $i, X22 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ X21)
% 0.71/0.91          | ~ (m1_subset_1 @ X22 @ X21)
% 0.71/0.91          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 0.71/0.91      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.71/0.91  thf('101', plain,
% 0.71/0.91      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.71/0.91          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.71/0.91        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['99', '100'])).
% 0.71/0.91  thf('102', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.71/0.91      inference('clc', [status(thm)], ['88', '89'])).
% 0.71/0.91  thf('103', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.91  thf('104', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['102', '103'])).
% 0.71/0.91  thf('105', plain,
% 0.71/0.91      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.71/0.91         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.71/0.91      inference('clc', [status(thm)], ['101', '104'])).
% 0.71/0.91  thf('106', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['96', '97', '98', '105'])).
% 0.71/0.91  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('108', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.71/0.91      inference('clc', [status(thm)], ['106', '107'])).
% 0.71/0.91  thf('109', plain,
% 0.71/0.91      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.71/0.91        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.71/0.91        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.91      inference('sup+', [status(thm)], ['81', '108'])).
% 0.71/0.91  thf('110', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('111', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.71/0.91      inference('clc', [status(thm)], ['109', '110'])).
% 0.71/0.91  thf('112', plain,
% 0.71/0.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['73', '111'])).
% 0.71/0.91  thf('113', plain,
% 0.71/0.91      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['0'])).
% 0.71/0.91  thf('114', plain,
% 0.71/0.91      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['112', '113'])).
% 0.71/0.91  thf('115', plain, ($false),
% 0.71/0.91      inference('sat_resolution*', [status(thm)], ['1', '71', '72', '114'])).
% 0.71/0.91  
% 0.71/0.91  % SZS output end Refutation
% 0.71/0.91  
% 0.71/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
