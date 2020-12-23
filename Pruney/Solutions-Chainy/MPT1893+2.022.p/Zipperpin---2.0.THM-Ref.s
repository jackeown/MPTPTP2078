%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8AiqMyFqBk

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:36 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  292 (13517 expanded)
%              Number of leaves         :   33 (3792 expanded)
%              Depth                    :   32
%              Number of atoms          : 2574 (215379 expanded)
%              Number of equality atoms :   78 (2185 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(t61_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( ( v3_pre_topc @ B @ A )
                | ( v4_pre_topc @ B @ A ) )
              & ( v3_tex_2 @ B @ A )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( ( v3_pre_topc @ B @ A )
                  | ( v4_pre_topc @ B @ A ) )
                & ( v3_tex_2 @ B @ A )
                & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_tex_2 @ X27 @ X28 )
      | ~ ( v1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_tdlat_3 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tops_1 @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_3 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_3 ) )
      = ( k2_pre_topc @ sk_A @ sk_B_3 ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_3 ) )
      = ( k2_pre_topc @ sk_A @ sk_B_3 ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('33',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_3 ) )
    = ( k2_pre_topc @ sk_A @ sk_B_3 ) ),
    inference(demod,[status(thm)],['30','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','37'])).

thf('39',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_3 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ sk_B_3 )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('41',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_3 @ sk_A )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v4_pre_topc @ X21 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('45',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_tops_1 @ X25 @ X26 )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ( v1_tops_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ( v1_tops_1 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('62',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('73',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60'])).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v4_pre_topc @ X21 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_tdlat_3 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ( ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60'])).

thf('85',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('93',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60'])).

thf('97',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['83','102'])).

thf('104',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('106',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( v4_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('107',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('114',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','37'])).

thf('116',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_3 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ sk_B_3 )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('118',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_3 @ sk_A )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('120',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('121',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('124',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('129',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('133',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('134',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_B_3 ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('140',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v4_pre_topc @ X21 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_tdlat_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
      | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','145'])).

thf('147',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('148',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('149',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['147','153'])).

thf('155',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['146','154'])).

thf('156',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('157',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('158',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','161'])).

thf('163',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('165',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('170',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('172',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('174',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['162','174'])).

thf('176',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['155','175'])).

thf('177',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('178',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('179',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('180',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_pre_topc @ X23 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_3 )
      | ~ ( v2_tex_2 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('185',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('186',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_3 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['181','182','183','189'])).

thf('191',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','190'])).

thf('192',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('193',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['177','193'])).

thf('195',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['162','174'])).

thf('196',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('201',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( sk_B @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( sk_B @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      = ( sk_B @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['199','206'])).

thf('208',plain,
    ( ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['176','207'])).

thf('209',plain,(
    ! [X16: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B @ X16 ) @ X16 )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('210',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('215',plain,(
    ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('217',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['215','216'])).

thf('218',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['103','217'])).

thf('219',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('220',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['181','182','183','189'])).

thf('222',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60'])).

thf('224',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('226',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('227',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60'])).

thf('228',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('229',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['226','231'])).

thf('233',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('234',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('236',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['225','234','235'])).

thf('237',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['215','216'])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('242',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('243',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( sk_B @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('245',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
        = ( sk_B @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
      = ( sk_B @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['215','216'])).

thf('249',plain,
    ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) ) )
    = ( sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
    = ( sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['240','249'])).

thf('251',plain,(
    v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['218','250'])).

thf('252',plain,(
    ! [X16: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B @ X16 ) @ X16 )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('253',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,(
    $false ),
    inference(demod,[status(thm)],['9','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8AiqMyFqBk
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.71/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.91  % Solved by: fo/fo7.sh
% 0.71/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.91  % done 1105 iterations in 0.455s
% 0.71/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.91  % SZS output start Refutation
% 0.71/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.71/0.91  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.71/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.91  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.71/0.91  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.71/0.91  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.71/0.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.71/0.91  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.71/0.91  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.71/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.91  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.71/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.91  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.71/0.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.71/0.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.71/0.91  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.71/0.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.71/0.91  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.71/0.91  thf(t61_tex_2, conjecture,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.71/0.91         ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.71/0.91                ( v3_tex_2 @ B @ A ) & 
% 0.71/0.91                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.71/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.91    (~( ![A:$i]:
% 0.71/0.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.71/0.91            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91          ( ![B:$i]:
% 0.71/0.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.71/0.91                   ( v3_tex_2 @ B @ A ) & 
% 0.71/0.91                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.71/0.91    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.71/0.91  thf('0', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t49_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.71/0.91         ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91           ( ( v3_tex_2 @ B @ A ) <=>
% 0.71/0.91             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.71/0.91  thf('1', plain,
% 0.71/0.91      (![X27 : $i, X28 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.71/0.91          | ~ (v3_tex_2 @ X27 @ X28)
% 0.71/0.91          | ~ (v1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.71/0.91          | ~ (l1_pre_topc @ X28)
% 0.71/0.91          | ~ (v1_tdlat_3 @ X28)
% 0.71/0.91          | ~ (v2_pre_topc @ X28)
% 0.71/0.91          | (v2_struct_0 @ X28))),
% 0.71/0.91      inference('cnf', [status(esa)], [t49_tex_2])).
% 0.71/0.91  thf('2', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (v1_tdlat_3 @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | ~ (v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.71/0.91        | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['0', '1'])).
% 0.71/0.91  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('5', plain, ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('6', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('7', plain, (((v2_struct_0 @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.71/0.91  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('9', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('clc', [status(thm)], ['7', '8'])).
% 0.71/0.91  thf('10', plain,
% 0.71/0.91      (((v3_pre_topc @ sk_B_3 @ sk_A) | (v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('11', plain,
% 0.71/0.91      (((v4_pre_topc @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['10'])).
% 0.71/0.91  thf('12', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t52_pre_topc, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( l1_pre_topc @ A ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.71/0.91             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.71/0.91               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.71/0.91  thf('13', plain,
% 0.71/0.91      (![X7 : $i, X8 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.71/0.91          | ~ (v4_pre_topc @ X7 @ X8)
% 0.71/0.91          | ((k2_pre_topc @ X8 @ X7) = (X7))
% 0.71/0.91          | ~ (l1_pre_topc @ X8))),
% 0.71/0.91      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.71/0.91  thf('14', plain,
% 0.71/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | ((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3))
% 0.71/0.91        | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.91  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('16', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3))
% 0.71/0.91        | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['14', '15'])).
% 0.71/0.91  thf('17', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['11', '16'])).
% 0.71/0.91  thf('18', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(dt_k2_pre_topc, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( ( l1_pre_topc @ A ) & 
% 0.71/0.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.91       ( m1_subset_1 @
% 0.71/0.91         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.71/0.91  thf('19', plain,
% 0.71/0.91      (![X5 : $i, X6 : $i]:
% 0.71/0.91         (~ (l1_pre_topc @ X5)
% 0.71/0.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.71/0.91          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.71/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.71/0.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.71/0.91  thf('20', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_3) @ 
% 0.71/0.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.71/0.91  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('22', plain,
% 0.71/0.91      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_3) @ 
% 0.71/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['20', '21'])).
% 0.71/0.91  thf(d2_tops_3, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( l1_pre_topc @ A ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91           ( ( v1_tops_1 @ B @ A ) <=>
% 0.71/0.91             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.71/0.91  thf('23', plain,
% 0.71/0.91      (![X11 : $i, X12 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.71/0.91          | ~ (v1_tops_1 @ X11 @ X12)
% 0.71/0.91          | ((k2_pre_topc @ X12 @ X11) = (u1_struct_0 @ X12))
% 0.71/0.91          | ~ (l1_pre_topc @ X12))),
% 0.71/0.91      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.71/0.91  thf('24', plain,
% 0.71/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_3))
% 0.71/0.91            = (u1_struct_0 @ sk_A))
% 0.71/0.91        | ~ (v1_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_3) @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['22', '23'])).
% 0.71/0.91  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('26', plain,
% 0.71/0.91      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_3) @ 
% 0.71/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['20', '21'])).
% 0.71/0.91  thf('27', plain,
% 0.71/0.91      (![X7 : $i, X8 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.71/0.91          | ~ (v4_pre_topc @ X7 @ X8)
% 0.71/0.91          | ((k2_pre_topc @ X8 @ X7) = (X7))
% 0.71/0.91          | ~ (l1_pre_topc @ X8))),
% 0.71/0.91      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.71/0.91  thf('28', plain,
% 0.71/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_3))
% 0.71/0.91            = (k2_pre_topc @ sk_A @ sk_B_3))
% 0.71/0.91        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B_3) @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.91  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('30', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_3))
% 0.71/0.91          = (k2_pre_topc @ sk_A @ sk_B_3))
% 0.71/0.91        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B_3) @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.91  thf('31', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(fc1_tops_1, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.71/0.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.91       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.71/0.91  thf('32', plain,
% 0.71/0.91      (![X9 : $i, X10 : $i]:
% 0.71/0.91         (~ (l1_pre_topc @ X9)
% 0.71/0.91          | ~ (v2_pre_topc @ X9)
% 0.71/0.91          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.71/0.91          | (v4_pre_topc @ (k2_pre_topc @ X9 @ X10) @ X9))),
% 0.71/0.91      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.71/0.91  thf('33', plain,
% 0.71/0.91      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B_3) @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['31', '32'])).
% 0.71/0.91  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('36', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B_3) @ sk_A)),
% 0.71/0.91      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.71/0.91  thf('37', plain,
% 0.71/0.91      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_3))
% 0.71/0.91         = (k2_pre_topc @ sk_A @ sk_B_3))),
% 0.71/0.91      inference('demod', [status(thm)], ['30', '36'])).
% 0.71/0.91  thf('38', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A))
% 0.71/0.91        | ~ (v1_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_3) @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['24', '25', '37'])).
% 0.71/0.91  thf('39', plain,
% 0.71/0.91      (((~ (v1_tops_1 @ sk_B_3 @ sk_A)
% 0.71/0.91         | ((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A))))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['17', '38'])).
% 0.71/0.91  thf('40', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['11', '16'])).
% 0.71/0.91  thf('41', plain,
% 0.71/0.91      (((~ (v1_tops_1 @ sk_B_3 @ sk_A) | ((sk_B_3) = (u1_struct_0 @ sk_A))))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['39', '40'])).
% 0.71/0.91  thf('42', plain,
% 0.71/0.91      (((v4_pre_topc @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['10'])).
% 0.71/0.91  thf('43', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t24_tdlat_3, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ( v3_tdlat_3 @ A ) <=>
% 0.71/0.91         ( ![B:$i]:
% 0.71/0.91           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.71/0.91  thf('44', plain,
% 0.71/0.91      (![X20 : $i, X21 : $i]:
% 0.71/0.91         (~ (v3_tdlat_3 @ X20)
% 0.71/0.91          | ~ (v4_pre_topc @ X21 @ X20)
% 0.71/0.91          | (v3_pre_topc @ X21 @ X20)
% 0.71/0.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.91          | ~ (l1_pre_topc @ X20)
% 0.71/0.91          | ~ (v2_pre_topc @ X20))),
% 0.71/0.91      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.71/0.91  thf('45', plain,
% 0.71/0.91      ((~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | (v3_pre_topc @ sk_B_3 @ sk_A)
% 0.71/0.91        | ~ (v4_pre_topc @ sk_B_3 @ sk_A)
% 0.71/0.91        | ~ (v3_tdlat_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.71/0.91  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('48', plain, ((v3_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('49', plain,
% 0.71/0.91      (((v3_pre_topc @ sk_B_3 @ sk_A) | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.71/0.91  thf('50', plain,
% 0.71/0.91      (((v3_pre_topc @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['42', '49'])).
% 0.71/0.91  thf('51', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t47_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.71/0.91             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.71/0.91  thf('52', plain,
% 0.71/0.91      (![X25 : $i, X26 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.71/0.91          | (v1_tops_1 @ X25 @ X26)
% 0.71/0.91          | ~ (v3_tex_2 @ X25 @ X26)
% 0.71/0.91          | ~ (v3_pre_topc @ X25 @ X26)
% 0.71/0.91          | ~ (l1_pre_topc @ X26)
% 0.71/0.91          | ~ (v2_pre_topc @ X26)
% 0.71/0.91          | (v2_struct_0 @ X26))),
% 0.71/0.91      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.71/0.91  thf('53', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | ~ (v3_pre_topc @ sk_B_3 @ sk_A)
% 0.71/0.91        | ~ (v3_tex_2 @ sk_B_3 @ sk_A)
% 0.71/0.91        | (v1_tops_1 @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['51', '52'])).
% 0.71/0.91  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('56', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('57', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ~ (v3_pre_topc @ sk_B_3 @ sk_A)
% 0.71/0.91        | (v1_tops_1 @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.71/0.91  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('59', plain,
% 0.71/0.91      (((v1_tops_1 @ sk_B_3 @ sk_A) | ~ (v3_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('clc', [status(thm)], ['57', '58'])).
% 0.71/0.91  thf('60', plain,
% 0.71/0.91      (((v1_tops_1 @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['50', '59'])).
% 0.71/0.91  thf('61', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['41', '60'])).
% 0.71/0.91  thf(t17_tdlat_3, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ( v1_tdlat_3 @ A ) <=>
% 0.71/0.91         ( ![B:$i]:
% 0.71/0.91           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.71/0.91  thf('62', plain,
% 0.71/0.91      (![X16 : $i]:
% 0.71/0.91         ((m1_subset_1 @ (sk_B @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.71/0.91          | (v1_tdlat_3 @ X16)
% 0.71/0.91          | ~ (l1_pre_topc @ X16)
% 0.71/0.91          | ~ (v2_pre_topc @ X16))),
% 0.71/0.91      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.71/0.91  thf('63', plain,
% 0.71/0.91      (![X5 : $i, X6 : $i]:
% 0.71/0.91         (~ (l1_pre_topc @ X5)
% 0.71/0.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.71/0.91          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.71/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.71/0.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.71/0.91  thf('64', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v2_pre_topc @ X0)
% 0.71/0.91          | ~ (l1_pre_topc @ X0)
% 0.71/0.91          | (v1_tdlat_3 @ X0)
% 0.71/0.91          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ 
% 0.71/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.71/0.91          | ~ (l1_pre_topc @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['62', '63'])).
% 0.71/0.91  thf('65', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ 
% 0.71/0.91           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.71/0.91          | (v1_tdlat_3 @ X0)
% 0.71/0.91          | ~ (l1_pre_topc @ X0)
% 0.71/0.91          | ~ (v2_pre_topc @ X0))),
% 0.71/0.91      inference('simplify', [status(thm)], ['64'])).
% 0.71/0.91  thf(t3_subset, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.91  thf('66', plain,
% 0.71/0.91      (![X2 : $i, X3 : $i]:
% 0.71/0.91         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('67', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v2_pre_topc @ X0)
% 0.71/0.91          | ~ (l1_pre_topc @ X0)
% 0.71/0.91          | (v1_tdlat_3 @ X0)
% 0.71/0.91          | (r1_tarski @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ (u1_struct_0 @ X0)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.71/0.91  thf('68', plain,
% 0.71/0.91      ((((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3)
% 0.71/0.91         | (v1_tdlat_3 @ sk_A)
% 0.71/0.91         | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91         | ~ (v2_pre_topc @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['61', '67'])).
% 0.71/0.91  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('71', plain,
% 0.71/0.91      ((((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3)
% 0.71/0.91         | (v1_tdlat_3 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.71/0.91  thf('72', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('clc', [status(thm)], ['7', '8'])).
% 0.71/0.91  thf('73', plain,
% 0.71/0.91      (((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['71', '72'])).
% 0.71/0.91  thf('74', plain,
% 0.71/0.91      (![X2 : $i, X4 : $i]:
% 0.71/0.91         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('75', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['73', '74'])).
% 0.71/0.91  thf('76', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['41', '60'])).
% 0.71/0.91  thf('77', plain,
% 0.71/0.91      (![X20 : $i, X21 : $i]:
% 0.71/0.91         (~ (v3_tdlat_3 @ X20)
% 0.71/0.91          | ~ (v4_pre_topc @ X21 @ X20)
% 0.71/0.91          | (v3_pre_topc @ X21 @ X20)
% 0.71/0.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.91          | ~ (l1_pre_topc @ X20)
% 0.71/0.91          | ~ (v2_pre_topc @ X20))),
% 0.71/0.91      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.71/0.91  thf('78', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91           | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91           | (v3_pre_topc @ X0 @ sk_A)
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.71/0.91           | ~ (v3_tdlat_3 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['76', '77'])).
% 0.71/0.91  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('81', plain, ((v3_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('82', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (v3_pre_topc @ X0 @ sk_A)
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.71/0.91  thf('83', plain,
% 0.71/0.91      (((~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A)
% 0.71/0.91         | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['75', '82'])).
% 0.71/0.91  thf('84', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['41', '60'])).
% 0.71/0.91  thf('85', plain,
% 0.71/0.91      (![X16 : $i]:
% 0.71/0.91         ((m1_subset_1 @ (sk_B @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.71/0.91          | (v1_tdlat_3 @ X16)
% 0.71/0.91          | ~ (l1_pre_topc @ X16)
% 0.71/0.91          | ~ (v2_pre_topc @ X16))),
% 0.71/0.91      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.71/0.91  thf('86', plain,
% 0.71/0.91      (![X2 : $i, X3 : $i]:
% 0.71/0.91         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('87', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v2_pre_topc @ X0)
% 0.71/0.91          | ~ (l1_pre_topc @ X0)
% 0.71/0.91          | (v1_tdlat_3 @ X0)
% 0.71/0.91          | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['85', '86'])).
% 0.71/0.91  thf('88', plain,
% 0.71/0.91      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3)
% 0.71/0.91         | (v1_tdlat_3 @ sk_A)
% 0.71/0.91         | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91         | ~ (v2_pre_topc @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['84', '87'])).
% 0.71/0.91  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('91', plain,
% 0.71/0.91      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3) | (v1_tdlat_3 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.71/0.91  thf('92', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('clc', [status(thm)], ['7', '8'])).
% 0.71/0.91  thf('93', plain,
% 0.71/0.91      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['91', '92'])).
% 0.71/0.91  thf('94', plain,
% 0.71/0.91      (![X2 : $i, X4 : $i]:
% 0.71/0.91         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('95', plain,
% 0.71/0.91      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_3)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['93', '94'])).
% 0.71/0.91  thf('96', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['41', '60'])).
% 0.71/0.91  thf('97', plain,
% 0.71/0.91      (![X9 : $i, X10 : $i]:
% 0.71/0.91         (~ (l1_pre_topc @ X9)
% 0.71/0.91          | ~ (v2_pre_topc @ X9)
% 0.71/0.91          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.71/0.91          | (v4_pre_topc @ (k2_pre_topc @ X9 @ X10) @ X9))),
% 0.71/0.91      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.71/0.91  thf('98', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (v4_pre_topc @ (k2_pre_topc @ sk_A @ X0) @ sk_A)
% 0.71/0.91           | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91           | ~ (l1_pre_topc @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['96', '97'])).
% 0.71/0.91  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('101', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (v4_pre_topc @ (k2_pre_topc @ sk_A @ X0) @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.71/0.91  thf('102', plain,
% 0.71/0.91      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['95', '101'])).
% 0.71/0.91  thf('103', plain,
% 0.71/0.91      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['83', '102'])).
% 0.71/0.91  thf('104', plain,
% 0.71/0.91      (((v3_pre_topc @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['10'])).
% 0.71/0.91  thf('105', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t23_tdlat_3, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ( v3_tdlat_3 @ A ) <=>
% 0.71/0.91         ( ![B:$i]:
% 0.71/0.91           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.71/0.91  thf('106', plain,
% 0.71/0.91      (![X18 : $i, X19 : $i]:
% 0.71/0.91         (~ (v3_tdlat_3 @ X18)
% 0.71/0.91          | ~ (v3_pre_topc @ X19 @ X18)
% 0.71/0.91          | (v4_pre_topc @ X19 @ X18)
% 0.71/0.91          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.71/0.91          | ~ (l1_pre_topc @ X18)
% 0.71/0.91          | ~ (v2_pre_topc @ X18))),
% 0.71/0.91      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.71/0.91  thf('107', plain,
% 0.71/0.91      ((~ (v2_pre_topc @ sk_A)
% 0.71/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | (v4_pre_topc @ sk_B_3 @ sk_A)
% 0.71/0.91        | ~ (v3_pre_topc @ sk_B_3 @ sk_A)
% 0.71/0.91        | ~ (v3_tdlat_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['105', '106'])).
% 0.71/0.91  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('110', plain, ((v3_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('111', plain,
% 0.71/0.91      (((v4_pre_topc @ sk_B_3 @ sk_A) | ~ (v3_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.71/0.91  thf('112', plain,
% 0.71/0.91      (((v4_pre_topc @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['104', '111'])).
% 0.71/0.91  thf('113', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3))
% 0.71/0.91        | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['14', '15'])).
% 0.71/0.91  thf('114', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['112', '113'])).
% 0.71/0.91  thf('115', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A))
% 0.71/0.91        | ~ (v1_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_3) @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['24', '25', '37'])).
% 0.71/0.91  thf('116', plain,
% 0.71/0.91      (((~ (v1_tops_1 @ sk_B_3 @ sk_A)
% 0.71/0.91         | ((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['114', '115'])).
% 0.71/0.91  thf('117', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['112', '113'])).
% 0.71/0.91  thf('118', plain,
% 0.71/0.91      (((~ (v1_tops_1 @ sk_B_3 @ sk_A) | ((sk_B_3) = (u1_struct_0 @ sk_A))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['116', '117'])).
% 0.71/0.91  thf('119', plain,
% 0.71/0.91      (((v3_pre_topc @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('split', [status(esa)], ['10'])).
% 0.71/0.91  thf('120', plain,
% 0.71/0.91      (((v1_tops_1 @ sk_B_3 @ sk_A) | ~ (v3_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('clc', [status(thm)], ['57', '58'])).
% 0.71/0.91  thf('121', plain,
% 0.71/0.91      (((v1_tops_1 @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['119', '120'])).
% 0.71/0.91  thf('122', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('123', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v2_pre_topc @ X0)
% 0.71/0.91          | ~ (l1_pre_topc @ X0)
% 0.71/0.91          | (v1_tdlat_3 @ X0)
% 0.71/0.91          | (r1_tarski @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ (u1_struct_0 @ X0)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.71/0.91  thf('124', plain,
% 0.71/0.91      ((((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3)
% 0.71/0.91         | (v1_tdlat_3 @ sk_A)
% 0.71/0.91         | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91         | ~ (v2_pre_topc @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['122', '123'])).
% 0.71/0.91  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('127', plain,
% 0.71/0.91      ((((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3)
% 0.71/0.91         | (v1_tdlat_3 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.71/0.91  thf('128', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('clc', [status(thm)], ['7', '8'])).
% 0.71/0.91  thf('129', plain,
% 0.71/0.91      (((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['127', '128'])).
% 0.71/0.91  thf('130', plain,
% 0.71/0.91      (![X2 : $i, X4 : $i]:
% 0.71/0.91         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('131', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['129', '130'])).
% 0.71/0.91  thf('132', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('133', plain,
% 0.71/0.91      (![X5 : $i, X6 : $i]:
% 0.71/0.91         (~ (l1_pre_topc @ X5)
% 0.71/0.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.71/0.91          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.71/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.71/0.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.71/0.91  thf('134', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (m1_subset_1 @ (k2_pre_topc @ sk_A @ X0) @ 
% 0.71/0.91              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.91           | ~ (l1_pre_topc @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['132', '133'])).
% 0.71/0.91  thf('135', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('137', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (m1_subset_1 @ (k2_pre_topc @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_B_3))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.71/0.91  thf('138', plain,
% 0.71/0.91      (((m1_subset_1 @ 
% 0.71/0.91         (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['131', '137'])).
% 0.71/0.91  thf('139', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('140', plain,
% 0.71/0.91      (![X20 : $i, X21 : $i]:
% 0.71/0.91         (~ (v3_tdlat_3 @ X20)
% 0.71/0.91          | ~ (v4_pre_topc @ X21 @ X20)
% 0.71/0.91          | (v3_pre_topc @ X21 @ X20)
% 0.71/0.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.91          | ~ (l1_pre_topc @ X20)
% 0.71/0.91          | ~ (v2_pre_topc @ X20))),
% 0.71/0.91      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.71/0.91  thf('141', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91           | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91           | (v3_pre_topc @ X0 @ sk_A)
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.71/0.91           | ~ (v3_tdlat_3 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['139', '140'])).
% 0.71/0.91  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('144', plain, ((v3_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('145', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (v3_pre_topc @ X0 @ sk_A)
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.71/0.91  thf('146', plain,
% 0.71/0.91      (((~ (v4_pre_topc @ 
% 0.71/0.91            (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) @ sk_A)
% 0.71/0.91         | (v3_pre_topc @ 
% 0.71/0.91            (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['138', '145'])).
% 0.71/0.91  thf('147', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['129', '130'])).
% 0.71/0.91  thf('148', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('149', plain,
% 0.71/0.91      (![X9 : $i, X10 : $i]:
% 0.71/0.91         (~ (l1_pre_topc @ X9)
% 0.71/0.91          | ~ (v2_pre_topc @ X9)
% 0.71/0.91          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.71/0.91          | (v4_pre_topc @ (k2_pre_topc @ X9 @ X10) @ X9))),
% 0.71/0.91      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.71/0.91  thf('150', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (v4_pre_topc @ (k2_pre_topc @ sk_A @ X0) @ sk_A)
% 0.71/0.91           | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91           | ~ (l1_pre_topc @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['148', '149'])).
% 0.71/0.91  thf('151', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('153', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (v4_pre_topc @ (k2_pre_topc @ sk_A @ X0) @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.71/0.91  thf('154', plain,
% 0.71/0.91      (((v4_pre_topc @ 
% 0.71/0.91         (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) @ sk_A))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['147', '153'])).
% 0.71/0.91  thf('155', plain,
% 0.71/0.91      (((v3_pre_topc @ 
% 0.71/0.91         (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) @ sk_A))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['146', '154'])).
% 0.71/0.91  thf('156', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['129', '130'])).
% 0.71/0.91  thf('157', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('158', plain,
% 0.71/0.91      (![X7 : $i, X8 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.71/0.91          | ~ (v4_pre_topc @ X7 @ X8)
% 0.71/0.91          | ((k2_pre_topc @ X8 @ X7) = (X7))
% 0.71/0.91          | ~ (l1_pre_topc @ X8))),
% 0.71/0.91      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.71/0.91  thf('159', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['157', '158'])).
% 0.71/0.91  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('161', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['159', '160'])).
% 0.71/0.91  thf('162', plain,
% 0.71/0.91      (((~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A)
% 0.71/0.91         | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91             = (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['156', '161'])).
% 0.71/0.91  thf('163', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('164', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v2_pre_topc @ X0)
% 0.71/0.91          | ~ (l1_pre_topc @ X0)
% 0.71/0.91          | (v1_tdlat_3 @ X0)
% 0.71/0.91          | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['85', '86'])).
% 0.71/0.91  thf('165', plain,
% 0.71/0.91      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3)
% 0.71/0.91         | (v1_tdlat_3 @ sk_A)
% 0.71/0.91         | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91         | ~ (v2_pre_topc @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['163', '164'])).
% 0.71/0.91  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('168', plain,
% 0.71/0.91      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3) | (v1_tdlat_3 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['165', '166', '167'])).
% 0.71/0.91  thf('169', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('clc', [status(thm)], ['7', '8'])).
% 0.71/0.91  thf('170', plain,
% 0.71/0.91      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['168', '169'])).
% 0.71/0.91  thf('171', plain,
% 0.71/0.91      (![X2 : $i, X4 : $i]:
% 0.71/0.91         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('172', plain,
% 0.71/0.91      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_3)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['170', '171'])).
% 0.71/0.91  thf('173', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | (v4_pre_topc @ (k2_pre_topc @ sk_A @ X0) @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.71/0.91  thf('174', plain,
% 0.71/0.91      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['172', '173'])).
% 0.71/0.91  thf('175', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91          = (k2_pre_topc @ sk_A @ (sk_B @ sk_A))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['162', '174'])).
% 0.71/0.91  thf('176', plain,
% 0.71/0.91      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['155', '175'])).
% 0.71/0.91  thf('177', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['129', '130'])).
% 0.71/0.91  thf('178', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('179', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(t41_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91           ( ( v2_tex_2 @ B @ A ) <=>
% 0.71/0.91             ( ![C:$i]:
% 0.71/0.91               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91                 ( ( r1_tarski @ C @ B ) =>
% 0.71/0.91                   ( ( k9_subset_1 @
% 0.71/0.91                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.71/0.91                     ( C ) ) ) ) ) ) ) ) ))).
% 0.71/0.91  thf('180', plain,
% 0.71/0.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.71/0.91          | ~ (v2_tex_2 @ X22 @ X23)
% 0.71/0.91          | ~ (r1_tarski @ X24 @ X22)
% 0.71/0.91          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.71/0.91              (k2_pre_topc @ X23 @ X24)) = (X24))
% 0.71/0.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.71/0.91          | ~ (l1_pre_topc @ X23)
% 0.71/0.91          | ~ (v2_pre_topc @ X23)
% 0.71/0.91          | (v2_struct_0 @ X23))),
% 0.71/0.91      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.71/0.91  thf('181', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((v2_struct_0 @ sk_A)
% 0.71/0.91          | ~ (v2_pre_topc @ sk_A)
% 0.71/0.91          | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.91          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 0.71/0.91              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.71/0.91          | ~ (r1_tarski @ X0 @ sk_B_3)
% 0.71/0.91          | ~ (v2_tex_2 @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['179', '180'])).
% 0.71/0.91  thf('182', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('184', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(d7_tex_2, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( l1_pre_topc @ A ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91           ( ( v3_tex_2 @ B @ A ) <=>
% 0.71/0.91             ( ( v2_tex_2 @ B @ A ) & 
% 0.71/0.91               ( ![C:$i]:
% 0.71/0.91                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.91                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.71/0.91                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.71/0.91  thf('185', plain,
% 0.71/0.91      (![X13 : $i, X14 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.71/0.91          | ~ (v3_tex_2 @ X13 @ X14)
% 0.71/0.91          | (v2_tex_2 @ X13 @ X14)
% 0.71/0.91          | ~ (l1_pre_topc @ X14))),
% 0.71/0.91      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.71/0.91  thf('186', plain,
% 0.71/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.91        | (v2_tex_2 @ sk_B_3 @ sk_A)
% 0.71/0.91        | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['184', '185'])).
% 0.71/0.91  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('188', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('189', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 0.71/0.91      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.71/0.91  thf('190', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((v2_struct_0 @ sk_A)
% 0.71/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.91          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 0.71/0.91              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.71/0.91          | ~ (r1_tarski @ X0 @ sk_B_3))),
% 0.71/0.91      inference('demod', [status(thm)], ['181', '182', '183', '189'])).
% 0.71/0.91  thf('191', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (r1_tarski @ X0 @ sk_B_3)
% 0.71/0.91           | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 0.71/0.91               (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.71/0.91           | (v2_struct_0 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['178', '190'])).
% 0.71/0.91  thf('192', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['118', '121'])).
% 0.71/0.91  thf('193', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (r1_tarski @ X0 @ sk_B_3)
% 0.71/0.91           | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ X0))
% 0.71/0.91               = (X0))
% 0.71/0.91           | (v2_struct_0 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['191', '192'])).
% 0.71/0.91  thf('194', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A))))
% 0.71/0.91             = (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91         | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['177', '193'])).
% 0.71/0.91  thf('195', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91          = (k2_pre_topc @ sk_A @ (sk_B @ sk_A))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['162', '174'])).
% 0.71/0.91  thf('196', plain,
% 0.71/0.91      (((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['127', '128'])).
% 0.71/0.91  thf('197', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91             = (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.71/0.91  thf('198', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('199', plain,
% 0.71/0.91      ((((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91          = (k2_pre_topc @ sk_A @ (sk_B @ sk_A))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['197', '198'])).
% 0.71/0.91  thf('200', plain,
% 0.71/0.91      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_3)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['170', '171'])).
% 0.71/0.91  thf('201', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (r1_tarski @ X0 @ sk_B_3)
% 0.71/0.91           | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ X0))
% 0.71/0.91               = (X0))
% 0.71/0.91           | (v2_struct_0 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['191', '192'])).
% 0.71/0.91  thf('202', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) = (sk_B @ sk_A))
% 0.71/0.91         | ~ (r1_tarski @ (sk_B @ sk_A) @ sk_B_3)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['200', '201'])).
% 0.71/0.91  thf('203', plain,
% 0.71/0.91      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['168', '169'])).
% 0.71/0.91  thf('204', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) = (sk_B @ sk_A))))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['202', '203'])).
% 0.71/0.91  thf('205', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('206', plain,
% 0.71/0.91      ((((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91          = (sk_B @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['204', '205'])).
% 0.71/0.91  thf('207', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['199', '206'])).
% 0.71/0.91  thf('208', plain,
% 0.71/0.91      (((v3_pre_topc @ (sk_B @ sk_A) @ sk_A))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['176', '207'])).
% 0.71/0.91  thf('209', plain,
% 0.71/0.91      (![X16 : $i]:
% 0.71/0.91         (~ (v3_pre_topc @ (sk_B @ X16) @ X16)
% 0.71/0.91          | (v1_tdlat_3 @ X16)
% 0.71/0.91          | ~ (l1_pre_topc @ X16)
% 0.71/0.91          | ~ (v2_pre_topc @ X16))),
% 0.71/0.91      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.71/0.91  thf('210', plain,
% 0.71/0.91      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v1_tdlat_3 @ sk_A)))
% 0.71/0.91         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['208', '209'])).
% 0.71/0.91  thf('211', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('212', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('213', plain,
% 0.71/0.91      (((v1_tdlat_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['210', '211', '212'])).
% 0.71/0.91  thf('214', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('clc', [status(thm)], ['7', '8'])).
% 0.71/0.91  thf('215', plain, (~ ((v3_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['213', '214'])).
% 0.71/0.91  thf('216', plain,
% 0.71/0.91      (((v4_pre_topc @ sk_B_3 @ sk_A)) | ((v3_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('split', [status(esa)], ['10'])).
% 0.71/0.91  thf('217', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sat_resolution*', [status(thm)], ['215', '216'])).
% 0.71/0.91  thf('218', plain,
% 0.71/0.91      ((v3_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A)),
% 0.71/0.91      inference('simpl_trail', [status(thm)], ['103', '217'])).
% 0.71/0.91  thf('219', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['73', '74'])).
% 0.71/0.91  thf('220', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['41', '60'])).
% 0.71/0.91  thf('221', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((v2_struct_0 @ sk_A)
% 0.71/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.91          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 0.71/0.91              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.71/0.91          | ~ (r1_tarski @ X0 @ sk_B_3))),
% 0.71/0.91      inference('demod', [status(thm)], ['181', '182', '183', '189'])).
% 0.71/0.91  thf('222', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (r1_tarski @ X0 @ sk_B_3)
% 0.71/0.91           | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 0.71/0.91               (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.71/0.91           | (v2_struct_0 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['220', '221'])).
% 0.71/0.91  thf('223', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['41', '60'])).
% 0.71/0.91  thf('224', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (r1_tarski @ X0 @ sk_B_3)
% 0.71/0.91           | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ X0))
% 0.71/0.91               = (X0))
% 0.71/0.91           | (v2_struct_0 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['222', '223'])).
% 0.71/0.91  thf('225', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A))))
% 0.71/0.91             = (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91         | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['219', '224'])).
% 0.71/0.91  thf('226', plain,
% 0.71/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ 
% 0.71/0.91         (k1_zfmisc_1 @ sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['73', '74'])).
% 0.71/0.91  thf('227', plain,
% 0.71/0.91      ((((sk_B_3) = (u1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['41', '60'])).
% 0.71/0.91  thf('228', plain,
% 0.71/0.91      (![X7 : $i, X8 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.71/0.91          | ~ (v4_pre_topc @ X7 @ X8)
% 0.71/0.91          | ((k2_pre_topc @ X8 @ X7) = (X7))
% 0.71/0.91          | ~ (l1_pre_topc @ X8))),
% 0.71/0.91      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.71/0.91  thf('229', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (l1_pre_topc @ sk_A)
% 0.71/0.91           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['227', '228'])).
% 0.71/0.91  thf('230', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('231', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.71/0.91           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['229', '230'])).
% 0.71/0.91  thf('232', plain,
% 0.71/0.91      (((~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A)
% 0.71/0.91         | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91             = (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['226', '231'])).
% 0.71/0.91  thf('233', plain,
% 0.71/0.91      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_A))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['95', '101'])).
% 0.71/0.91  thf('234', plain,
% 0.71/0.91      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91          = (k2_pre_topc @ sk_A @ (sk_B @ sk_A))))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['232', '233'])).
% 0.71/0.91  thf('235', plain,
% 0.71/0.91      (((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)) @ sk_B_3))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['71', '72'])).
% 0.71/0.91  thf('236', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91             = (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['225', '234', '235'])).
% 0.71/0.91  thf('237', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sat_resolution*', [status(thm)], ['215', '216'])).
% 0.71/0.91  thf('238', plain,
% 0.71/0.91      (((v2_struct_0 @ sk_A)
% 0.71/0.91        | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91            (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91            = (k2_pre_topc @ sk_A @ (sk_B @ sk_A))))),
% 0.71/0.91      inference('simpl_trail', [status(thm)], ['236', '237'])).
% 0.71/0.91  thf('239', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('240', plain,
% 0.71/0.91      (((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91         = (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['238', '239'])).
% 0.71/0.91  thf('241', plain,
% 0.71/0.91      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_3)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['93', '94'])).
% 0.71/0.91  thf('242', plain,
% 0.71/0.91      ((![X0 : $i]:
% 0.71/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 0.71/0.91           | ~ (r1_tarski @ X0 @ sk_B_3)
% 0.71/0.91           | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ X0))
% 0.71/0.91               = (X0))
% 0.71/0.91           | (v2_struct_0 @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['222', '223'])).
% 0.71/0.91  thf('243', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) = (sk_B @ sk_A))
% 0.71/0.91         | ~ (r1_tarski @ (sk_B @ sk_A) @ sk_B_3)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['241', '242'])).
% 0.71/0.91  thf('244', plain,
% 0.71/0.91      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['91', '92'])).
% 0.71/0.91  thf('245', plain,
% 0.71/0.91      ((((v2_struct_0 @ sk_A)
% 0.71/0.91         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 0.71/0.91             (k2_pre_topc @ sk_A @ (sk_B @ sk_A))) = (sk_B @ sk_A))))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('demod', [status(thm)], ['243', '244'])).
% 0.71/0.91  thf('246', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('247', plain,
% 0.71/0.91      ((((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91          = (sk_B @ sk_A)))
% 0.71/0.91         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 0.71/0.91      inference('clc', [status(thm)], ['245', '246'])).
% 0.71/0.91  thf('248', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 0.71/0.91      inference('sat_resolution*', [status(thm)], ['215', '216'])).
% 0.71/0.91  thf('249', plain,
% 0.71/0.91      (((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ (sk_B @ sk_A)))
% 0.71/0.91         = (sk_B @ sk_A))),
% 0.71/0.91      inference('simpl_trail', [status(thm)], ['247', '248'])).
% 0.71/0.91  thf('250', plain, (((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A))),
% 0.71/0.91      inference('sup+', [status(thm)], ['240', '249'])).
% 0.71/0.91  thf('251', plain, ((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 0.71/0.91      inference('demod', [status(thm)], ['218', '250'])).
% 0.71/0.91  thf('252', plain,
% 0.71/0.91      (![X16 : $i]:
% 0.71/0.91         (~ (v3_pre_topc @ (sk_B @ X16) @ X16)
% 0.71/0.91          | (v1_tdlat_3 @ X16)
% 0.71/0.91          | ~ (l1_pre_topc @ X16)
% 0.71/0.91          | ~ (v2_pre_topc @ X16))),
% 0.71/0.91      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.71/0.91  thf('253', plain,
% 0.71/0.91      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v1_tdlat_3 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['251', '252'])).
% 0.71/0.91  thf('254', plain, ((v2_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('255', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('256', plain, ((v1_tdlat_3 @ sk_A)),
% 0.71/0.91      inference('demod', [status(thm)], ['253', '254', '255'])).
% 0.71/0.91  thf('257', plain, ($false), inference('demod', [status(thm)], ['9', '256'])).
% 0.71/0.91  
% 0.71/0.91  % SZS output end Refutation
% 0.71/0.91  
% 0.71/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
