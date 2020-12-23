%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKvI8w3DpA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 273 expanded)
%              Number of leaves         :   35 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  812 (2504 expanded)
%              Number of equality atoms :   56 ( 165 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf('14',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tops_1 @ X27 @ X28 )
      | ~ ( v3_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ X23 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X25 @ ( k2_tops_1 @ X26 @ X25 ) )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t93_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_tops_1 @ X29 @ X30 )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ~ ( v2_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t93_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('48',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('50',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['29','48','49'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','50'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('53',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('77',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['13','51','76'])).

thf('78',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['28'])).

thf('79',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['29','48'])).

thf('80',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKvI8w3DpA
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 102 iterations in 0.025s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.46  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.46  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.46  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(t94_tops_1, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.46             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( l1_pre_topc @ A ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46              ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.46                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(l78_tops_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.46             ( k7_subset_1 @
% 0.21/0.46               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.46               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X21 : $i, X22 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.46          | ((k2_tops_1 @ X22 @ X21)
% 0.21/0.46              = (k7_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.21/0.46                 (k2_pre_topc @ X22 @ X21) @ (k1_tops_1 @ X22 @ X21)))
% 0.21/0.46          | ~ (l1_pre_topc @ X22))),
% 0.21/0.46      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.46            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.46               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t52_pre_topc, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.46             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.46               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X19 : $i, X20 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.46          | ~ (v4_pre_topc @ X19 @ X20)
% 0.21/0.46          | ((k2_pre_topc @ X20 @ X19) = (X19))
% 0.21/0.46          | ~ (l1_pre_topc @ X20))),
% 0.21/0.46      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.21/0.46        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.21/0.46          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.46           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.46         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t92_tops_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X27 : $i, X28 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.46          | (v2_tops_1 @ X27 @ X28)
% 0.21/0.46          | ~ (v3_tops_1 @ X27 @ X28)
% 0.21/0.46          | ~ (l1_pre_topc @ X28))),
% 0.21/0.46      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.21/0.46        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('20', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t84_tops_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.46             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X23 : $i, X24 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.46          | ~ (v2_tops_1 @ X23 @ X24)
% 0.21/0.46          | ((k1_tops_1 @ X24 @ X23) = (k1_xboole_0))
% 0.21/0.46          | ~ (l1_pre_topc @ X24))),
% 0.21/0.46      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.46        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.46  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('26', plain,
% 0.21/0.46      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.46        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.46         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['21', '26'])).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('split', [status(esa)], ['28'])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.46         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('split', [status(esa)], ['14'])).
% 0.21/0.46  thf('31', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t88_tops_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.46             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.46  thf('32', plain,
% 0.21/0.46      (![X25 : $i, X26 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.46          | ~ (r1_tarski @ X25 @ (k2_tops_1 @ X26 @ X25))
% 0.21/0.46          | (v2_tops_1 @ X25 @ X26)
% 0.21/0.46          | ~ (l1_pre_topc @ X26))),
% 0.21/0.46      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.46        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.46  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      (((v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.46        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.21/0.46         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.46  thf(d10_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.46  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.46      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.46  thf('39', plain,
% 0.21/0.46      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('demod', [status(thm)], ['36', '38'])).
% 0.21/0.46  thf('40', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t93_tops_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.21/0.46             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.46  thf('41', plain,
% 0.21/0.46      (![X29 : $i, X30 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.46          | (v3_tops_1 @ X29 @ X30)
% 0.21/0.46          | ~ (v4_pre_topc @ X29 @ X30)
% 0.21/0.46          | ~ (v2_tops_1 @ X29 @ X30)
% 0.21/0.46          | ~ (l1_pre_topc @ X30))),
% 0.21/0.46      inference('cnf', [status(esa)], [t93_tops_1])).
% 0.21/0.46  thf('42', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | ~ (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.46        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.46        | (v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.46  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('44', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('45', plain, ((~ (v2_tops_1 @ sk_B @ sk_A) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.46  thf('46', plain,
% 0.21/0.46      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['39', '45'])).
% 0.21/0.46  thf('47', plain,
% 0.21/0.46      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['28'])).
% 0.21/0.46  thf('48', plain,
% 0.21/0.46      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.46  thf('49', plain,
% 0.21/0.46      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('split', [status(esa)], ['14'])).
% 0.21/0.46  thf('50', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['29', '48', '49'])).
% 0.21/0.46  thf('51', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['27', '50'])).
% 0.21/0.46  thf(dt_k2_subset_1, axiom,
% 0.21/0.46    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.46  thf('52', plain,
% 0.21/0.46      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.46  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.46  thf('53', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.46  thf('54', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.46      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.46  thf(dt_k3_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.46  thf('55', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.21/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.46  thf('56', plain,
% 0.21/0.46      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.46  thf('57', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.46      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.46  thf(d5_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.46  thf('58', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]:
% 0.21/0.46         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.21/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.46  thf('59', plain,
% 0.21/0.46      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.46  thf('60', plain,
% 0.21/0.46      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['56', '59'])).
% 0.21/0.46  thf('61', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]:
% 0.21/0.46         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.21/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.46  thf('62', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.21/0.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.46  thf('63', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.46      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.46  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.46  thf('64', plain,
% 0.21/0.46      (![X11 : $i, X12 : $i]:
% 0.21/0.46         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.21/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.46      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.46  thf('65', plain,
% 0.21/0.46      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.46  thf('66', plain,
% 0.21/0.46      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.46  thf('67', plain,
% 0.21/0.46      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.46  thf('68', plain,
% 0.21/0.46      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['62', '67'])).
% 0.21/0.46  thf('69', plain,
% 0.21/0.46      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['62', '67'])).
% 0.21/0.46  thf(t38_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.21/0.46       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf('70', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.46  thf('71', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.21/0.46          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.46  thf('72', plain,
% 0.21/0.46      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['56', '59'])).
% 0.21/0.46  thf(t3_subset, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.46  thf('73', plain,
% 0.21/0.46      (![X16 : $i, X17 : $i]:
% 0.21/0.46         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.46  thf('74', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)),
% 0.21/0.46      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.46  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['71', '74'])).
% 0.21/0.46  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['68', '75'])).
% 0.21/0.46  thf('77', plain, (((k2_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '51', '76'])).
% 0.21/0.46  thf('78', plain,
% 0.21/0.46      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.46         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('split', [status(esa)], ['28'])).
% 0.21/0.46  thf('79', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['29', '48'])).
% 0.21/0.46  thf('80', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.21/0.46  thf('81', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['77', '80'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
