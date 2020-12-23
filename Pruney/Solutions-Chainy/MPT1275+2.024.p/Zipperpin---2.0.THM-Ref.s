%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0vzldarO7C

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 586 expanded)
%              Number of leaves         :   31 ( 170 expanded)
%              Depth                    :   15
%              Number of atoms          :  899 (6740 expanded)
%              Number of equality atoms :   51 ( 376 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tops_1 @ X27 @ X28 )
      | ( r1_tarski @ X27 @ ( k2_tops_1 @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v2_tops_1 @ X29 @ X30 )
      | ~ ( v3_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ ( k2_tops_1 @ X28 @ X27 ) )
      | ( v2_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X20 @ X19 ) @ X20 )
      | ( v3_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','34'])).

thf('36',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('38',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('40',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','38','39'])).

thf('41',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['12','40'])).

thf('42',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','41'])).

thf('43',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf('60',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('62',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_B )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( ( k3_subset_1 @ sk_B @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','70'])).

thf('72',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','38','39'])).

thf('73',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ sk_B @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','73'])).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ sk_B )
    | ( ( k3_subset_1 @ sk_B @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf('78',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('79',plain,
    ( ( sk_B
     != ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( sk_B
       != ( k2_tops_1 @ sk_A @ sk_B ) )
      & ( v3_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k3_subset_1 @ sk_B @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('81',plain,
    ( ( sk_B
     != ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
   <= ( ( sk_B
       != ( k2_tops_1 @ sk_A @ sk_B ) )
      & ( v3_tops_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','38'])).

thf('83',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','38','39'])).

thf('84',plain,(
    sk_B
 != ( k3_subset_1 @ sk_B @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['76','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','38','39'])).

thf('90',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ sk_B ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['85','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0vzldarO7C
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:53:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 181 iterations in 0.084s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.19/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.19/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.53  thf(t94_tops_1, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.53             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( l1_pre_topc @ A ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53              ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.53                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t88_tops_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.19/0.53             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X27 : $i, X28 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.53          | ~ (v2_tops_1 @ X27 @ X28)
% 0.19/0.53          | (r1_tarski @ X27 @ (k2_tops_1 @ X28 @ X27))
% 0.19/0.53          | ~ (l1_pre_topc @ X28))),
% 0.19/0.53      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('split', [status(esa)], ['5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t92_tops_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X29 : $i, X30 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.19/0.53          | (v2_tops_1 @ X29 @ X30)
% 0.19/0.53          | ~ (v3_tops_1 @ X29 @ X30)
% 0.19/0.53          | ~ (l1_pre_topc @ X30))),
% 0.19/0.53      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.19/0.53        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('11', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['6', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('split', [status(esa)], ['13'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.19/0.53         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.53      inference('split', [status(esa)], ['5'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X27 : $i, X28 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.53          | ~ (r1_tarski @ X27 @ (k2_tops_1 @ X28 @ X27))
% 0.19/0.53          | (v2_tops_1 @ X27 @ X28)
% 0.19/0.53          | ~ (l1_pre_topc @ X28))),
% 0.19/0.53      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.53        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.53  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (((v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.53        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.19/0.53         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['15', '20'])).
% 0.19/0.53  thf(d10_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.53  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.53      inference('demod', [status(thm)], ['21', '23'])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d5_tops_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v3_tops_1 @ B @ A ) <=>
% 0.19/0.53             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.53          | ~ (v2_tops_1 @ (k2_pre_topc @ X20 @ X19) @ X20)
% 0.19/0.53          | (v3_tops_1 @ X19 @ X20)
% 0.19/0.53          | ~ (l1_pre_topc @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (v3_tops_1 @ sk_B @ sk_A)
% 0.19/0.53        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.53  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t52_pre_topc, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.19/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.19/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X17 : $i, X18 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.53          | ~ (v4_pre_topc @ X17 @ X18)
% 0.19/0.53          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.19/0.53          | ~ (l1_pre_topc @ X18))),
% 0.19/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.19/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('33', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('34', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.19/0.53  thf('35', plain, (((v3_tops_1 @ sk_B @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['27', '28', '34'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['24', '35'])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('split', [status(esa)], ['13'])).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('split', [status(esa)], ['5'])).
% 0.19/0.53  thf('40', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['14', '38', '39'])).
% 0.19/0.53  thf('41', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.19/0.53      inference('simpl_trail', [status(thm)], ['12', '40'])).
% 0.19/0.53  thf('42', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['4', '41'])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['6', '11'])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t84_tops_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.19/0.53             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.36/0.53  thf('45', plain,
% 0.36/0.53      (![X25 : $i, X26 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.53          | ~ (v2_tops_1 @ X25 @ X26)
% 0.36/0.53          | ((k1_tops_1 @ X26 @ X25) = (k1_xboole_0))
% 0.36/0.53          | ~ (l1_pre_topc @ X26))),
% 0.36/0.53      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.53  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['43', '48'])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(l78_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.53             ( k7_subset_1 @
% 0.36/0.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.36/0.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      (![X21 : $i, X22 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.53          | ((k2_tops_1 @ X22 @ X21)
% 0.36/0.53              = (k7_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.36/0.53                 (k2_pre_topc @ X22 @ X21) @ (k1_tops_1 @ X22 @ X21)))
% 0.36/0.53          | ~ (l1_pre_topc @ X22))),
% 0.36/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.53  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('54', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.36/0.53  thf('55', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.53  thf('56', plain,
% 0.36/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.36/0.53          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.53  thf('57', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.53  thf('58', plain,
% 0.36/0.53      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.53         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['52', '53', '54', '57'])).
% 0.36/0.53  thf('59', plain,
% 0.36/0.53      ((((k2_tops_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['49', '58'])).
% 0.36/0.53  thf('60', plain,
% 0.36/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['43', '48'])).
% 0.36/0.53  thf('61', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t44_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.36/0.53  thf('62', plain,
% 0.36/0.53      (![X23 : $i, X24 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.36/0.53          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 0.36/0.53          | ~ (l1_pre_topc @ X24))),
% 0.36/0.53      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.36/0.53  thf('63', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.53  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('65', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.53      inference('demod', [status(thm)], ['63', '64'])).
% 0.36/0.53  thf('66', plain,
% 0.36/0.53      (((r1_tarski @ k1_xboole_0 @ sk_B)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['60', '65'])).
% 0.36/0.53  thf(t3_subset, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.53  thf('67', plain,
% 0.36/0.53      (![X14 : $i, X16 : $i]:
% 0.36/0.53         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('68', plain,
% 0.36/0.53      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_B)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.53  thf(d5_subset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.53  thf('69', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i]:
% 0.36/0.53         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.36/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.53  thf('70', plain,
% 0.36/0.53      ((((k3_subset_1 @ sk_B @ k1_xboole_0)
% 0.36/0.53          = (k4_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.36/0.53  thf('71', plain,
% 0.36/0.53      ((((k2_tops_1 @ sk_A @ sk_B) = (k3_subset_1 @ sk_B @ k1_xboole_0)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['59', '70'])).
% 0.36/0.53  thf('72', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('sat_resolution*', [status(thm)], ['14', '38', '39'])).
% 0.36/0.53  thf('73', plain,
% 0.36/0.53      (((k2_tops_1 @ sk_A @ sk_B) = (k3_subset_1 @ sk_B @ k1_xboole_0))),
% 0.36/0.53      inference('simpl_trail', [status(thm)], ['71', '72'])).
% 0.36/0.53  thf('74', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_B @ k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['42', '73'])).
% 0.36/0.53  thf('75', plain,
% 0.36/0.53      (![X0 : $i, X2 : $i]:
% 0.36/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('76', plain,
% 0.36/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ sk_B)
% 0.36/0.53        | ((k3_subset_1 @ sk_B @ k1_xboole_0) = (sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['74', '75'])).
% 0.36/0.53  thf('77', plain,
% 0.36/0.53      ((((k2_tops_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['49', '58'])).
% 0.36/0.53  thf('78', plain,
% 0.36/0.53      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.53         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.53      inference('split', [status(esa)], ['13'])).
% 0.36/0.53  thf('79', plain,
% 0.36/0.53      ((((sk_B) != (k4_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.36/0.53         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) & 
% 0.36/0.53             ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.53  thf('80', plain,
% 0.36/0.53      ((((k3_subset_1 @ sk_B @ k1_xboole_0)
% 0.36/0.53          = (k4_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.36/0.53  thf('81', plain,
% 0.36/0.53      ((((sk_B) != (k3_subset_1 @ sk_B @ k1_xboole_0)))
% 0.36/0.53         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) & 
% 0.36/0.53             ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.53  thf('82', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sat_resolution*', [status(thm)], ['14', '38'])).
% 0.36/0.53  thf('83', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('sat_resolution*', [status(thm)], ['14', '38', '39'])).
% 0.36/0.53  thf('84', plain, (((sk_B) != (k3_subset_1 @ sk_B @ k1_xboole_0))),
% 0.36/0.53      inference('simpl_trail', [status(thm)], ['81', '82', '83'])).
% 0.36/0.53  thf('85', plain, (~ (r1_tarski @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ sk_B)),
% 0.36/0.53      inference('simplify_reflect-', [status(thm)], ['76', '84'])).
% 0.36/0.53  thf('86', plain,
% 0.36/0.53      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_B)))
% 0.36/0.53         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.53  thf(dt_k3_subset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.53  thf('87', plain,
% 0.36/0.53      (![X7 : $i, X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 0.36/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.36/0.53  thf('88', plain,
% 0.36/0.53      (((m1_subset_1 @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ 
% 0.36/0.53         (k1_zfmisc_1 @ sk_B))) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.36/0.53  thf('89', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('sat_resolution*', [status(thm)], ['14', '38', '39'])).
% 0.36/0.53  thf('90', plain,
% 0.36/0.53      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ (k1_zfmisc_1 @ sk_B))),
% 0.36/0.53      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 0.36/0.53  thf('91', plain,
% 0.36/0.53      (![X14 : $i, X15 : $i]:
% 0.36/0.53         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('92', plain, ((r1_tarski @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ sk_B)),
% 0.36/0.53      inference('sup-', [status(thm)], ['90', '91'])).
% 0.36/0.53  thf('93', plain, ($false), inference('demod', [status(thm)], ['85', '92'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
