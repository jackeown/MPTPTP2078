%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ln9i3WR9uD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:33 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 408 expanded)
%              Number of leaves         :   32 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  766 (4628 expanded)
%              Number of equality atoms :   53 ( 277 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tops_1 @ X30 @ X31 )
      | ( r1_tarski @ X30 @ ( k2_tops_1 @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tops_1 @ X32 @ X33 )
      | ~ ( v3_tops_1 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r1_tarski @ X30 @ ( k2_tops_1 @ X31 @ X30 ) )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X25 @ X24 ) @ X25 )
      | ( v3_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','33'])).

thf('35',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['13','37','38'])).

thf('40',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['11','39'])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','40'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ X26 ) @ ( k1_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('49',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tops_1 @ X28 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X28 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['13','37','38'])).

thf('57',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48','57','60'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('62',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['43','61','72'])).

thf('74',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('75',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['13','37'])).

thf('76',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48','57','60'])).

thf('78',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ln9i3WR9uD
% 0.15/0.37  % Computer   : n005.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 09:58:33 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 119 iterations in 0.041s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.53  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.23/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.23/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.53  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.23/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.53  thf(t94_tops_1, conjecture,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53           ( ( v4_pre_topc @ B @ A ) =>
% 0.23/0.53             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i]:
% 0.23/0.53        ( ( l1_pre_topc @ A ) =>
% 0.23/0.53          ( ![B:$i]:
% 0.23/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53              ( ( v4_pre_topc @ B @ A ) =>
% 0.23/0.53                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.23/0.53  thf('0', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(t88_tops_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.23/0.53             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.23/0.53  thf('1', plain,
% 0.23/0.53      (![X30 : $i, X31 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.23/0.53          | ~ (v2_tops_1 @ X30 @ X31)
% 0.23/0.53          | (r1_tarski @ X30 @ (k2_tops_1 @ X31 @ X30))
% 0.23/0.53          | ~ (l1_pre_topc @ X31))),
% 0.23/0.53      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.23/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.23/0.53      inference('split', [status(esa)], ['4'])).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(t92_tops_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.23/0.53  thf('7', plain,
% 0.23/0.53      (![X32 : $i, X33 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.23/0.53          | (v2_tops_1 @ X32 @ X33)
% 0.23/0.53          | ~ (v3_tops_1 @ X32 @ X33)
% 0.23/0.53          | ~ (l1_pre_topc @ X33))),
% 0.23/0.53      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.23/0.53        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.53  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('10', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.23/0.53  thf('11', plain,
% 0.23/0.53      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.23/0.53  thf('12', plain,
% 0.23/0.53      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('split', [status(esa)], ['12'])).
% 0.23/0.53  thf('14', plain,
% 0.23/0.53      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.23/0.53         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.23/0.53      inference('split', [status(esa)], ['4'])).
% 0.23/0.53  thf('15', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      (![X30 : $i, X31 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.23/0.53          | ~ (r1_tarski @ X30 @ (k2_tops_1 @ X31 @ X30))
% 0.23/0.53          | (v2_tops_1 @ X30 @ X31)
% 0.23/0.53          | ~ (l1_pre_topc @ X31))),
% 0.23/0.53      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.23/0.53  thf('17', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | (v2_tops_1 @ sk_B @ sk_A)
% 0.23/0.53        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('19', plain,
% 0.23/0.53      (((v2_tops_1 @ sk_B @ sk_A)
% 0.23/0.53        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.23/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.23/0.53  thf('20', plain,
% 0.23/0.53      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.23/0.53         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['14', '19'])).
% 0.23/0.53  thf(d10_xboole_0, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.23/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.53  thf('22', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.23/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.53  thf('23', plain,
% 0.23/0.53      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.23/0.53      inference('demod', [status(thm)], ['20', '22'])).
% 0.23/0.53  thf('24', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(d5_tops_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53           ( ( v3_tops_1 @ B @ A ) <=>
% 0.23/0.53             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.23/0.53  thf('25', plain,
% 0.23/0.53      (![X24 : $i, X25 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.23/0.53          | ~ (v2_tops_1 @ (k2_pre_topc @ X25 @ X24) @ X25)
% 0.23/0.53          | (v3_tops_1 @ X24 @ X25)
% 0.23/0.53          | ~ (l1_pre_topc @ X25))),
% 0.23/0.53      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | (v3_tops_1 @ sk_B @ sk_A)
% 0.23/0.53        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('28', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(t52_pre_topc, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.23/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.23/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.23/0.53  thf('29', plain,
% 0.23/0.53      (![X22 : $i, X23 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.23/0.53          | ~ (v4_pre_topc @ X22 @ X23)
% 0.23/0.53          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.23/0.53          | ~ (l1_pre_topc @ X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.23/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.53  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('32', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.23/0.53  thf('34', plain, (((v3_tops_1 @ sk_B @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['26', '27', '33'])).
% 0.23/0.53  thf('35', plain,
% 0.23/0.53      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['23', '34'])).
% 0.23/0.53  thf('36', plain,
% 0.23/0.53      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.23/0.53      inference('split', [status(esa)], ['12'])).
% 0.23/0.53  thf('37', plain,
% 0.23/0.53      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.23/0.53  thf('38', plain,
% 0.23/0.53      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.23/0.53      inference('split', [status(esa)], ['4'])).
% 0.23/0.53  thf('39', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('sat_resolution*', [status(thm)], ['13', '37', '38'])).
% 0.23/0.53  thf('40', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.23/0.53      inference('simpl_trail', [status(thm)], ['11', '39'])).
% 0.23/0.53  thf('41', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['2', '3', '40'])).
% 0.23/0.53  thf(t28_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (![X8 : $i, X9 : $i]:
% 0.23/0.53         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.23/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.53  thf('43', plain,
% 0.23/0.53      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.53  thf('44', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(l78_tops_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53           ( ( k2_tops_1 @ A @ B ) =
% 0.23/0.53             ( k7_subset_1 @
% 0.23/0.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.23/0.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.23/0.53  thf('45', plain,
% 0.23/0.53      (![X26 : $i, X27 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.23/0.53          | ((k2_tops_1 @ X27 @ X26)
% 0.23/0.53              = (k7_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.23/0.53                 (k2_pre_topc @ X27 @ X26) @ (k1_tops_1 @ X27 @ X26)))
% 0.23/0.53          | ~ (l1_pre_topc @ X27))),
% 0.23/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.23/0.53  thf('46', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.23/0.53  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('48', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.23/0.53  thf('49', plain,
% 0.23/0.53      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.23/0.53  thf('50', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(t84_tops_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.23/0.53             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.23/0.53  thf('51', plain,
% 0.23/0.53      (![X28 : $i, X29 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.23/0.53          | ~ (v2_tops_1 @ X28 @ X29)
% 0.23/0.53          | ((k1_tops_1 @ X29 @ X28) = (k1_xboole_0))
% 0.23/0.53          | ~ (l1_pre_topc @ X29))),
% 0.23/0.53      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.23/0.53  thf('52', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.23/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.23/0.53  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('54', plain,
% 0.23/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.23/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.23/0.53  thf('55', plain,
% 0.23/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.23/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['49', '54'])).
% 0.23/0.53  thf('56', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.23/0.53      inference('sat_resolution*', [status(thm)], ['13', '37', '38'])).
% 0.23/0.53  thf('57', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.23/0.53      inference('simpl_trail', [status(thm)], ['55', '56'])).
% 0.23/0.53  thf('58', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.23/0.53  thf('59', plain,
% 0.23/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.23/0.53          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.23/0.53  thf('60', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.23/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.23/0.53  thf('61', plain,
% 0.23/0.53      (((k2_tops_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['46', '47', '48', '57', '60'])).
% 0.23/0.53  thf(t4_subset_1, axiom,
% 0.23/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.53  thf('62', plain,
% 0.23/0.53      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.23/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.53  thf(t3_subset, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.53  thf('63', plain,
% 0.23/0.53      (![X16 : $i, X17 : $i]:
% 0.23/0.53         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.53  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.23/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.23/0.53  thf('65', plain,
% 0.23/0.53      (![X8 : $i, X9 : $i]:
% 0.23/0.53         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.23/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.53  thf('66', plain,
% 0.23/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.23/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.53  thf('67', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.53  thf('68', plain,
% 0.23/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['66', '67'])).
% 0.23/0.53  thf(t48_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.53  thf('69', plain,
% 0.23/0.53      (![X10 : $i, X11 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.23/0.53           = (k3_xboole_0 @ X10 @ X11))),
% 0.23/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.23/0.53  thf('70', plain,
% 0.23/0.53      (![X10 : $i, X11 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.23/0.53           = (k3_xboole_0 @ X10 @ X11))),
% 0.23/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.23/0.53  thf('71', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.23/0.53           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['69', '70'])).
% 0.23/0.53  thf('72', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.23/0.53           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['68', '71'])).
% 0.23/0.53  thf('73', plain, (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['43', '61', '72'])).
% 0.23/0.53  thf('74', plain,
% 0.23/0.53      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.23/0.53         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.23/0.53      inference('split', [status(esa)], ['12'])).
% 0.23/0.53  thf('75', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.23/0.53      inference('sat_resolution*', [status(thm)], ['13', '37'])).
% 0.23/0.53  thf('76', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.23/0.53      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.23/0.53  thf('77', plain,
% 0.23/0.53      (((k2_tops_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['46', '47', '48', '57', '60'])).
% 0.23/0.53  thf('78', plain, (((sk_B) != (k4_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.23/0.53  thf('79', plain, ($false),
% 0.23/0.53      inference('simplify_reflect-', [status(thm)], ['73', '78'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
