%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cvXsSr3fQ4

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:26 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 568 expanded)
%              Number of leaves         :   40 ( 164 expanded)
%              Depth                    :   21
%              Number of atoms          : 1369 (5950 expanded)
%              Number of equality atoms :   51 ( 121 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X50 @ X49 ) @ ( k2_tops_1 @ X50 @ X49 ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ X0 @ sk_B_1 )
        | ~ ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X46 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('27',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k1_tops_1 @ X52 @ X51 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X51 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( r1_tarski @ X25 @ ( k3_subset_1 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ ( k3_subset_1 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v1_tops_1 @ X40 @ X41 )
      | ( ( k2_pre_topc @ X41 @ X40 )
        = ( k2_struct_0 @ X41 ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('56',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tops_1 @ X42 @ X43 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X43 ) @ X42 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('62',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','34','61'])).

thf('63',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['60','62'])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','64'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('66',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_pre_topc @ X37 @ ( k3_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 ) ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('74',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v2_tops_1 @ X51 @ X52 )
      | ( ( k1_tops_1 @ X52 @ X51 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','34','61'])).

thf('81',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['72','81'])).

thf('83',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','63'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','84'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('86',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('87',plain,(
    r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('89',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ X34 @ ( k2_pre_topc @ X35 @ X34 ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('93',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,(
    r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('99',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_tops_1 @ X39 @ X38 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ X38 ) @ ( k2_pre_topc @ X39 @ ( k3_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 ) ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('104',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['100','101','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('107',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k2_tops_1 @ X48 @ X47 )
        = ( k2_tops_1 @ X48 @ ( k3_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('111',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','63'])).

thf('113',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('115',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('118',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','111','112','119'])).

thf('121',plain,(
    r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['97','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['36','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cvXsSr3fQ4
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:05:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.88/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.88/1.04  % Solved by: fo/fo7.sh
% 0.88/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.04  % done 1551 iterations in 0.593s
% 0.88/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.88/1.04  % SZS output start Refutation
% 0.88/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.88/1.04  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.88/1.04  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.88/1.04  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.88/1.04  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.88/1.04  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.88/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.88/1.04  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.88/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.88/1.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.88/1.04  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.88/1.04  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.88/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.88/1.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.88/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.88/1.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.88/1.04  thf(t88_tops_1, conjecture,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( ( v2_tops_1 @ B @ A ) <=>
% 0.88/1.04             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.88/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.04    (~( ![A:$i]:
% 0.88/1.04        ( ( l1_pre_topc @ A ) =>
% 0.88/1.04          ( ![B:$i]:
% 0.88/1.04            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04              ( ( v2_tops_1 @ B @ A ) <=>
% 0.88/1.04                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.88/1.04    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.88/1.04  thf('0', plain,
% 0.88/1.04      ((~ (r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 0.88/1.04        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('1', plain,
% 0.88/1.04      ((~ (r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.88/1.04         <= (~ ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('split', [status(esa)], ['0'])).
% 0.88/1.04  thf('2', plain,
% 0.88/1.04      (~ ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))) | 
% 0.88/1.04       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('split', [status(esa)], ['0'])).
% 0.88/1.04  thf('3', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(t73_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.88/1.04  thf('4', plain,
% 0.88/1.04      (![X49 : $i, X50 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.88/1.04          | (r1_xboole_0 @ (k1_tops_1 @ X50 @ X49) @ (k2_tops_1 @ X50 @ X49))
% 0.88/1.04          | ~ (l1_pre_topc @ X50))),
% 0.88/1.04      inference('cnf', [status(esa)], [t73_tops_1])).
% 0.88/1.04  thf('5', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.88/1.04           (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['3', '4'])).
% 0.88/1.04  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('7', plain,
% 0.88/1.04      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_tops_1 @ sk_A @ sk_B_1))),
% 0.88/1.04      inference('demod', [status(thm)], ['5', '6'])).
% 0.88/1.04  thf('8', plain,
% 0.88/1.04      (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 0.88/1.04        | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('9', plain,
% 0.88/1.04      (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.88/1.04         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('split', [status(esa)], ['8'])).
% 0.88/1.04  thf(d10_xboole_0, axiom,
% 0.88/1.04    (![A:$i,B:$i]:
% 0.88/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.88/1.04  thf('10', plain,
% 0.88/1.04      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.88/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.88/1.04  thf('11', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.88/1.04      inference('simplify', [status(thm)], ['10'])).
% 0.88/1.04  thf(t64_xboole_1, axiom,
% 0.88/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.88/1.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.88/1.04         ( r1_xboole_0 @ B @ D ) ) =>
% 0.88/1.04       ( r1_xboole_0 @ A @ C ) ))).
% 0.88/1.04  thf('12', plain,
% 0.88/1.04      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.88/1.04         ((r1_xboole_0 @ X11 @ X12)
% 0.88/1.04          | ~ (r1_tarski @ X11 @ X13)
% 0.88/1.04          | ~ (r1_tarski @ X12 @ X14)
% 0.88/1.04          | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.88/1.04      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.88/1.04  thf('13', plain,
% 0.88/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.04         (~ (r1_xboole_0 @ X0 @ X1)
% 0.88/1.04          | ~ (r1_tarski @ X2 @ X1)
% 0.88/1.04          | (r1_xboole_0 @ X0 @ X2))),
% 0.88/1.04      inference('sup-', [status(thm)], ['11', '12'])).
% 0.88/1.04  thf('14', plain,
% 0.88/1.04      ((![X0 : $i]:
% 0.88/1.04          ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.88/1.04           | ~ (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B_1))))
% 0.88/1.04         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['9', '13'])).
% 0.88/1.04  thf('15', plain,
% 0.88/1.04      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.88/1.04         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['7', '14'])).
% 0.88/1.04  thf('16', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.88/1.04      inference('simplify', [status(thm)], ['10'])).
% 0.88/1.04  thf(t67_xboole_1, axiom,
% 0.88/1.04    (![A:$i,B:$i,C:$i]:
% 0.88/1.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.88/1.04         ( r1_xboole_0 @ B @ C ) ) =>
% 0.88/1.04       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.88/1.04  thf('17', plain,
% 0.88/1.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.88/1.04         (((X15) = (k1_xboole_0))
% 0.88/1.04          | ~ (r1_tarski @ X15 @ X16)
% 0.88/1.04          | ~ (r1_tarski @ X15 @ X17)
% 0.88/1.04          | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.88/1.04      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.88/1.04  thf('18', plain,
% 0.88/1.04      (![X0 : $i, X1 : $i]:
% 0.88/1.04         (~ (r1_xboole_0 @ X0 @ X1)
% 0.88/1.04          | ~ (r1_tarski @ X0 @ X1)
% 0.88/1.04          | ((X0) = (k1_xboole_0)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.88/1.04  thf('19', plain,
% 0.88/1.04      (((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.88/1.04         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.88/1.04         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['15', '18'])).
% 0.88/1.04  thf('20', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(t44_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.88/1.04  thf('21', plain,
% 0.88/1.04      (![X45 : $i, X46 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.88/1.04          | (r1_tarski @ (k1_tops_1 @ X46 @ X45) @ X45)
% 0.88/1.04          | ~ (l1_pre_topc @ X46))),
% 0.88/1.04      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.88/1.04  thf('22', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.88/1.04      inference('sup-', [status(thm)], ['20', '21'])).
% 0.88/1.04  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('24', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.88/1.04      inference('demod', [status(thm)], ['22', '23'])).
% 0.88/1.04  thf('25', plain,
% 0.88/1.04      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.88/1.04         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('demod', [status(thm)], ['19', '24'])).
% 0.88/1.04  thf('26', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(t84_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( ( v2_tops_1 @ B @ A ) <=>
% 0.88/1.04             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.88/1.04  thf('27', plain,
% 0.88/1.04      (![X51 : $i, X52 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.88/1.04          | ((k1_tops_1 @ X52 @ X51) != (k1_xboole_0))
% 0.88/1.04          | (v2_tops_1 @ X51 @ X52)
% 0.88/1.04          | ~ (l1_pre_topc @ X52))),
% 0.88/1.04      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.88/1.04  thf('28', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.88/1.04        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['26', '27'])).
% 0.88/1.04  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('30', plain,
% 0.88/1.04      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.88/1.04        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.88/1.04      inference('demod', [status(thm)], ['28', '29'])).
% 0.88/1.04  thf('31', plain,
% 0.88/1.04      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.88/1.04         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['25', '30'])).
% 0.88/1.04  thf('32', plain,
% 0.88/1.04      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.88/1.04         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.88/1.04      inference('simplify', [status(thm)], ['31'])).
% 0.88/1.04  thf('33', plain,
% 0.88/1.04      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.88/1.04      inference('split', [status(esa)], ['0'])).
% 0.88/1.04  thf('34', plain,
% 0.88/1.04      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.88/1.04       ~ ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['32', '33'])).
% 0.88/1.04  thf('35', plain, (~ ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('sat_resolution*', [status(thm)], ['2', '34'])).
% 0.88/1.04  thf('36', plain, (~ (r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))),
% 0.88/1.04      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 0.88/1.04  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.88/1.04  thf('37', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.88/1.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.88/1.04  thf('38', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(t35_subset_1, axiom,
% 0.88/1.04    (![A:$i,B:$i]:
% 0.88/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.04       ( ![C:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.04           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.88/1.04             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.88/1.04  thf('39', plain,
% 0.88/1.04      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.88/1.04          | (r1_tarski @ X25 @ (k3_subset_1 @ X26 @ X27))
% 0.88/1.04          | ~ (r1_tarski @ X27 @ (k3_subset_1 @ X26 @ X25))
% 0.88/1.04          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.88/1.04      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.88/1.04  thf('40', plain,
% 0.88/1.04      (![X0 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.88/1.04          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04          | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['38', '39'])).
% 0.88/1.04  thf('41', plain,
% 0.88/1.04      (((r1_tarski @ sk_B_1 @ 
% 0.88/1.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.88/1.04        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['37', '40'])).
% 0.88/1.04  thf('42', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(dt_k3_subset_1, axiom,
% 0.88/1.04    (![A:$i,B:$i]:
% 0.88/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.04       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.88/1.04  thf('43', plain,
% 0.88/1.04      (![X18 : $i, X19 : $i]:
% 0.88/1.04         ((m1_subset_1 @ (k3_subset_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.88/1.04          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.88/1.04      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.88/1.04  thf('44', plain,
% 0.88/1.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.88/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['42', '43'])).
% 0.88/1.04  thf(dt_k2_pre_topc, axiom,
% 0.88/1.04    (![A:$i,B:$i]:
% 0.88/1.04     ( ( ( l1_pre_topc @ A ) & 
% 0.88/1.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.88/1.04       ( m1_subset_1 @
% 0.88/1.04         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.88/1.04  thf('45', plain,
% 0.88/1.04      (![X32 : $i, X33 : $i]:
% 0.88/1.04         (~ (l1_pre_topc @ X32)
% 0.88/1.04          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.88/1.04          | (m1_subset_1 @ (k2_pre_topc @ X32 @ X33) @ 
% 0.88/1.04             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.88/1.04      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.88/1.04  thf('46', plain,
% 0.88/1.04      (((m1_subset_1 @ 
% 0.88/1.04         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.88/1.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.88/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.88/1.04      inference('sup-', [status(thm)], ['44', '45'])).
% 0.88/1.04  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('48', plain,
% 0.88/1.04      ((m1_subset_1 @ 
% 0.88/1.04        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.88/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('demod', [status(thm)], ['46', '47'])).
% 0.88/1.04  thf('49', plain,
% 0.88/1.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.88/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['42', '43'])).
% 0.88/1.04  thf(d3_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( ( v1_tops_1 @ B @ A ) <=>
% 0.88/1.04             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.88/1.04  thf('50', plain,
% 0.88/1.04      (![X40 : $i, X41 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.88/1.04          | ~ (v1_tops_1 @ X40 @ X41)
% 0.88/1.04          | ((k2_pre_topc @ X41 @ X40) = (k2_struct_0 @ X41))
% 0.88/1.04          | ~ (l1_pre_topc @ X41))),
% 0.88/1.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.88/1.04  thf('51', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04            = (k2_struct_0 @ sk_A))
% 0.88/1.04        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.88/1.04      inference('sup-', [status(thm)], ['49', '50'])).
% 0.88/1.04  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('53', plain,
% 0.88/1.04      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04          = (k2_struct_0 @ sk_A))
% 0.88/1.04        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['51', '52'])).
% 0.88/1.04  thf('54', plain,
% 0.88/1.04      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.88/1.04      inference('split', [status(esa)], ['8'])).
% 0.88/1.04  thf('55', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(d4_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( ( v2_tops_1 @ B @ A ) <=>
% 0.88/1.04             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.88/1.04  thf('56', plain,
% 0.88/1.04      (![X42 : $i, X43 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.88/1.04          | ~ (v2_tops_1 @ X42 @ X43)
% 0.88/1.04          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X43) @ X42) @ X43)
% 0.88/1.04          | ~ (l1_pre_topc @ X43))),
% 0.88/1.04      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.88/1.04  thf('57', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.88/1.04        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('sup-', [status(thm)], ['55', '56'])).
% 0.88/1.04  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('59', plain,
% 0.88/1.04      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.88/1.04        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.88/1.04  thf('60', plain,
% 0.88/1.04      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.88/1.04         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['54', '59'])).
% 0.88/1.04  thf('61', plain,
% 0.88/1.04      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.88/1.04       ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('split', [status(esa)], ['8'])).
% 0.88/1.04  thf('62', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('sat_resolution*', [status(thm)], ['2', '34', '61'])).
% 0.88/1.04  thf('63', plain,
% 0.88/1.04      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.88/1.04      inference('simpl_trail', [status(thm)], ['60', '62'])).
% 0.88/1.04  thf('64', plain,
% 0.88/1.04      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04         = (k2_struct_0 @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['53', '63'])).
% 0.88/1.04  thf('65', plain,
% 0.88/1.04      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.88/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('demod', [status(thm)], ['48', '64'])).
% 0.88/1.04  thf(involutiveness_k3_subset_1, axiom,
% 0.88/1.04    (![A:$i,B:$i]:
% 0.88/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.04       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.88/1.04  thf('66', plain,
% 0.88/1.04      (![X20 : $i, X21 : $i]:
% 0.88/1.04         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.88/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.88/1.04      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.88/1.04  thf('67', plain,
% 0.88/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.88/1.04         = (k2_struct_0 @ sk_A))),
% 0.88/1.04      inference('sup-', [status(thm)], ['65', '66'])).
% 0.88/1.04  thf('68', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(d1_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( ( k1_tops_1 @ A @ B ) =
% 0.88/1.04             ( k3_subset_1 @
% 0.88/1.04               ( u1_struct_0 @ A ) @ 
% 0.88/1.04               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.88/1.04  thf('69', plain,
% 0.88/1.04      (![X36 : $i, X37 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.88/1.04          | ((k1_tops_1 @ X37 @ X36)
% 0.88/1.04              = (k3_subset_1 @ (u1_struct_0 @ X37) @ 
% 0.88/1.04                 (k2_pre_topc @ X37 @ (k3_subset_1 @ (u1_struct_0 @ X37) @ X36))))
% 0.88/1.04          | ~ (l1_pre_topc @ X37))),
% 0.88/1.04      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.88/1.04  thf('70', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 0.88/1.04            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04               (k2_pre_topc @ sk_A @ 
% 0.88/1.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['68', '69'])).
% 0.88/1.04  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('72', plain,
% 0.88/1.04      (((k1_tops_1 @ sk_A @ sk_B_1)
% 0.88/1.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.88/1.04      inference('demod', [status(thm)], ['70', '71'])).
% 0.88/1.04  thf('73', plain,
% 0.88/1.04      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.88/1.04      inference('split', [status(esa)], ['8'])).
% 0.88/1.04  thf('74', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('75', plain,
% 0.88/1.04      (![X51 : $i, X52 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.88/1.04          | ~ (v2_tops_1 @ X51 @ X52)
% 0.88/1.04          | ((k1_tops_1 @ X52 @ X51) = (k1_xboole_0))
% 0.88/1.04          | ~ (l1_pre_topc @ X52))),
% 0.88/1.04      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.88/1.04  thf('76', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.88/1.04        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('sup-', [status(thm)], ['74', '75'])).
% 0.88/1.04  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('78', plain,
% 0.88/1.04      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.88/1.04        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['76', '77'])).
% 0.88/1.04  thf('79', plain,
% 0.88/1.04      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.88/1.04         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['73', '78'])).
% 0.88/1.04  thf('80', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.88/1.04      inference('sat_resolution*', [status(thm)], ['2', '34', '61'])).
% 0.88/1.04  thf('81', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.88/1.04      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.88/1.04  thf('82', plain,
% 0.88/1.04      (((k1_xboole_0)
% 0.88/1.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.88/1.04      inference('demod', [status(thm)], ['72', '81'])).
% 0.88/1.04  thf('83', plain,
% 0.88/1.04      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04         = (k2_struct_0 @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['53', '63'])).
% 0.88/1.04  thf('84', plain,
% 0.88/1.04      (((k1_xboole_0)
% 0.88/1.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 0.88/1.04      inference('demod', [status(thm)], ['82', '83'])).
% 0.88/1.04  thf('85', plain,
% 0.88/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.88/1.04         = (k2_struct_0 @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['67', '84'])).
% 0.88/1.04  thf(t4_subset_1, axiom,
% 0.88/1.04    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.88/1.04  thf('86', plain,
% 0.88/1.04      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.88/1.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.88/1.04  thf('87', plain, ((r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['41', '85', '86'])).
% 0.88/1.04  thf('88', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf(t48_pre_topc, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.88/1.04  thf('89', plain,
% 0.88/1.04      (![X34 : $i, X35 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.88/1.04          | (r1_tarski @ X34 @ (k2_pre_topc @ X35 @ X34))
% 0.88/1.04          | ~ (l1_pre_topc @ X35))),
% 0.88/1.04      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.88/1.04  thf('90', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['88', '89'])).
% 0.88/1.04  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('92', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 0.88/1.04      inference('demod', [status(thm)], ['90', '91'])).
% 0.88/1.04  thf(t19_xboole_1, axiom,
% 0.88/1.04    (![A:$i,B:$i,C:$i]:
% 0.88/1.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.88/1.04       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.88/1.04  thf('93', plain,
% 0.88/1.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.88/1.04         (~ (r1_tarski @ X5 @ X6)
% 0.88/1.04          | ~ (r1_tarski @ X5 @ X7)
% 0.88/1.04          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.88/1.04      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.88/1.04  thf('94', plain,
% 0.88/1.04      (![X0 : $i]:
% 0.88/1.04         ((r1_tarski @ sk_B_1 @ 
% 0.88/1.04           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))
% 0.88/1.04          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.88/1.04      inference('sup-', [status(thm)], ['92', '93'])).
% 0.88/1.04  thf('95', plain,
% 0.88/1.04      ((r1_tarski @ sk_B_1 @ 
% 0.88/1.04        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ (k2_struct_0 @ sk_A)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['87', '94'])).
% 0.88/1.04  thf(commutativity_k3_xboole_0, axiom,
% 0.88/1.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.88/1.04  thf('96', plain,
% 0.88/1.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.88/1.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.88/1.04  thf('97', plain,
% 0.88/1.04      ((r1_tarski @ sk_B_1 @ 
% 0.88/1.04        (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('demod', [status(thm)], ['95', '96'])).
% 0.88/1.04  thf('98', plain,
% 0.88/1.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.88/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['42', '43'])).
% 0.88/1.04  thf(d2_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( ( k2_tops_1 @ A @ B ) =
% 0.88/1.04             ( k9_subset_1 @
% 0.88/1.04               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.88/1.04               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.88/1.04  thf('99', plain,
% 0.88/1.04      (![X38 : $i, X39 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.88/1.04          | ((k2_tops_1 @ X39 @ X38)
% 0.88/1.04              = (k9_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.88/1.04                 (k2_pre_topc @ X39 @ X38) @ 
% 0.88/1.04                 (k2_pre_topc @ X39 @ (k3_subset_1 @ (u1_struct_0 @ X39) @ X38))))
% 0.88/1.04          | ~ (l1_pre_topc @ X39))),
% 0.88/1.04      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.88/1.04  thf('100', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04               (k2_pre_topc @ sk_A @ 
% 0.88/1.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.88/1.04               (k2_pre_topc @ sk_A @ 
% 0.88/1.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['98', '99'])).
% 0.88/1.04  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('102', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('103', plain,
% 0.88/1.04      (![X20 : $i, X21 : $i]:
% 0.88/1.04         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.88/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.88/1.04      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.88/1.04  thf('104', plain,
% 0.88/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.88/1.04      inference('sup-', [status(thm)], ['102', '103'])).
% 0.88/1.04  thf('105', plain,
% 0.88/1.04      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.88/1.04            (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('demod', [status(thm)], ['100', '101', '104'])).
% 0.88/1.04  thf('106', plain,
% 0.88/1.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.88/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['42', '43'])).
% 0.88/1.04  thf(t62_tops_1, axiom,
% 0.88/1.04    (![A:$i]:
% 0.88/1.04     ( ( l1_pre_topc @ A ) =>
% 0.88/1.04       ( ![B:$i]:
% 0.88/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.04           ( ( k2_tops_1 @ A @ B ) =
% 0.88/1.04             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.88/1.04  thf('107', plain,
% 0.88/1.04      (![X47 : $i, X48 : $i]:
% 0.88/1.04         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.88/1.04          | ((k2_tops_1 @ X48 @ X47)
% 0.88/1.04              = (k2_tops_1 @ X48 @ (k3_subset_1 @ (u1_struct_0 @ X48) @ X47)))
% 0.88/1.04          | ~ (l1_pre_topc @ X48))),
% 0.88/1.04      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.88/1.04  thf('108', plain,
% 0.88/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.04        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04            = (k2_tops_1 @ sk_A @ 
% 0.88/1.04               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.88/1.04      inference('sup-', [status(thm)], ['106', '107'])).
% 0.88/1.04  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('110', plain,
% 0.88/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.88/1.04      inference('sup-', [status(thm)], ['102', '103'])).
% 0.88/1.04  thf('111', plain,
% 0.88/1.04      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 0.88/1.04      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.88/1.04  thf('112', plain,
% 0.88/1.04      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.88/1.04         = (k2_struct_0 @ sk_A))),
% 0.88/1.04      inference('demod', [status(thm)], ['53', '63'])).
% 0.88/1.04  thf('113', plain,
% 0.88/1.04      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('114', plain,
% 0.88/1.04      (![X32 : $i, X33 : $i]:
% 0.88/1.04         (~ (l1_pre_topc @ X32)
% 0.88/1.04          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.88/1.04          | (m1_subset_1 @ (k2_pre_topc @ X32 @ X33) @ 
% 0.88/1.04             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.88/1.04      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.88/1.04  thf('115', plain,
% 0.88/1.04      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.88/1.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.88/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.88/1.04      inference('sup-', [status(thm)], ['113', '114'])).
% 0.88/1.04  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.04  thf('117', plain,
% 0.88/1.04      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.88/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.04      inference('demod', [status(thm)], ['115', '116'])).
% 0.88/1.04  thf(redefinition_k9_subset_1, axiom,
% 0.88/1.04    (![A:$i,B:$i,C:$i]:
% 0.88/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.04       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.88/1.04  thf('118', plain,
% 0.88/1.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.88/1.04         (((k9_subset_1 @ X24 @ X22 @ X23) = (k3_xboole_0 @ X22 @ X23))
% 0.88/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.88/1.04      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.88/1.04  thf('119', plain,
% 0.88/1.04      (![X0 : $i]:
% 0.88/1.04         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.88/1.04           (k2_pre_topc @ sk_A @ sk_B_1))
% 0.88/1.04           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('sup-', [status(thm)], ['117', '118'])).
% 0.88/1.04  thf('120', plain,
% 0.88/1.04      (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.88/1.04         = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.88/1.04      inference('demod', [status(thm)], ['105', '111', '112', '119'])).
% 0.88/1.04  thf('121', plain, ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))),
% 0.88/1.04      inference('demod', [status(thm)], ['97', '120'])).
% 0.88/1.04  thf('122', plain, ($false), inference('demod', [status(thm)], ['36', '121'])).
% 0.88/1.04  
% 0.88/1.04  % SZS output end Refutation
% 0.88/1.04  
% 0.88/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
