%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.maVfKDpmfL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:26 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 700 expanded)
%              Number of leaves         :   39 ( 201 expanded)
%              Depth                    :   22
%              Number of atoms          : 1656 (7518 expanded)
%              Number of equality atoms :   50 ( 129 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X51 @ X50 ) @ ( k2_tops_1 @ X51 @ X50 ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ X0 @ sk_B )
        | ~ ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('21',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X45 @ X44 ) @ X44 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k1_tops_1 @ X53 @ X52 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t44_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X29 @ X27 )
      | ( r1_xboole_0 @ X29 @ ( k3_subset_1 @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t44_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('49',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('53',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('57',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('62',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('66',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_tops_1 @ X47 @ X46 )
        = ( k2_tops_1 @ X47 @ ( k3_subset_1 @ ( u1_struct_0 @ X47 ) @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('75',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v1_tops_1 @ X38 @ X39 )
      | ( ( k2_pre_topc @ X39 @ X38 )
        = ( k2_struct_0 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('81',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v2_tops_1 @ X40 @ X41 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 ) @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('87',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','34','86'])).

thf('88',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','88'])).

thf('90',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','89'])).

thf('91',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','90'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('92',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('96',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','88'])).

thf('102',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_xboole_0 @ X29 @ ( k3_subset_1 @ X28 @ X27 ) )
      | ( r1_tarski @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t44_subset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('106',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_pre_topc @ X37 @ ( k3_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 ) ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v2_tops_1 @ X52 @ X53 )
      | ( ( k1_tops_1 @ X53 @ X52 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','34','86'])).

thf('118',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','118'])).

thf('120',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','88'])).

thf('121',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['104','121'])).

thf('123',plain,
    ( ~ ( r1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','122'])).

thf('124',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('125',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','128'])).

thf('130',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['94','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('132',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( r1_tarski @ X24 @ ( k3_subset_1 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ X26 @ ( k3_subset_1 @ X25 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('136',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('137',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['36','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.maVfKDpmfL
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.33/2.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.58  % Solved by: fo/fo7.sh
% 2.33/2.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.58  % done 3327 iterations in 2.130s
% 2.33/2.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.58  % SZS output start Refutation
% 2.33/2.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.33/2.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.33/2.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.33/2.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.33/2.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.33/2.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.33/2.58  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 2.33/2.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.33/2.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.33/2.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.33/2.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.33/2.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.33/2.58  thf(sk_B_type, type, sk_B: $i).
% 2.33/2.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.33/2.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.33/2.58  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.58  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 2.33/2.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.33/2.58  thf(t88_tops_1, conjecture,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( ( v2_tops_1 @ B @ A ) <=>
% 2.33/2.58             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.33/2.58  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.58    (~( ![A:$i]:
% 2.33/2.58        ( ( l1_pre_topc @ A ) =>
% 2.33/2.58          ( ![B:$i]:
% 2.33/2.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58              ( ( v2_tops_1 @ B @ A ) <=>
% 2.33/2.58                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 2.33/2.58    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 2.33/2.58  thf('0', plain,
% 2.33/2.58      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.33/2.58        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('1', plain,
% 2.33/2.58      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.33/2.58         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('split', [status(esa)], ['0'])).
% 2.33/2.58  thf('2', plain,
% 2.33/2.58      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 2.33/2.58       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.58      inference('split', [status(esa)], ['0'])).
% 2.33/2.58  thf('3', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(t73_tops_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 2.33/2.58  thf('4', plain,
% 2.33/2.58      (![X50 : $i, X51 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 2.33/2.58          | (r1_xboole_0 @ (k1_tops_1 @ X51 @ X50) @ (k2_tops_1 @ X51 @ X50))
% 2.33/2.58          | ~ (l1_pre_topc @ X51))),
% 2.33/2.58      inference('cnf', [status(esa)], [t73_tops_1])).
% 2.33/2.58  thf('5', plain,
% 2.33/2.58      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.58        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['3', '4'])).
% 2.33/2.58  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('7', plain,
% 2.33/2.58      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.58      inference('demod', [status(thm)], ['5', '6'])).
% 2.33/2.58  thf('8', plain,
% 2.33/2.58      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.33/2.58        | (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('9', plain,
% 2.33/2.58      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.33/2.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('split', [status(esa)], ['8'])).
% 2.33/2.58  thf(d10_xboole_0, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.33/2.58  thf('10', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.33/2.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.33/2.58  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.33/2.58      inference('simplify', [status(thm)], ['10'])).
% 2.33/2.58  thf(t64_xboole_1, axiom,
% 2.33/2.58    (![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 2.33/2.58         ( r1_xboole_0 @ B @ D ) ) =>
% 2.33/2.58       ( r1_xboole_0 @ A @ C ) ))).
% 2.33/2.58  thf('12', plain,
% 2.33/2.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.33/2.58         ((r1_xboole_0 @ X4 @ X5)
% 2.33/2.58          | ~ (r1_tarski @ X4 @ X6)
% 2.33/2.58          | ~ (r1_tarski @ X5 @ X7)
% 2.33/2.58          | ~ (r1_xboole_0 @ X6 @ X7))),
% 2.33/2.58      inference('cnf', [status(esa)], [t64_xboole_1])).
% 2.33/2.58  thf('13', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.58         (~ (r1_xboole_0 @ X0 @ X1)
% 2.33/2.58          | ~ (r1_tarski @ X2 @ X1)
% 2.33/2.58          | (r1_xboole_0 @ X0 @ X2))),
% 2.33/2.58      inference('sup-', [status(thm)], ['11', '12'])).
% 2.33/2.58  thf('14', plain,
% 2.33/2.58      ((![X0 : $i]:
% 2.33/2.58          ((r1_xboole_0 @ X0 @ sk_B)
% 2.33/2.58           | ~ (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 2.33/2.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['9', '13'])).
% 2.33/2.58  thf('15', plain,
% 2.33/2.58      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))
% 2.33/2.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['7', '14'])).
% 2.33/2.58  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.33/2.58      inference('simplify', [status(thm)], ['10'])).
% 2.33/2.58  thf(t67_xboole_1, axiom,
% 2.33/2.58    (![A:$i,B:$i,C:$i]:
% 2.33/2.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 2.33/2.58         ( r1_xboole_0 @ B @ C ) ) =>
% 2.33/2.58       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.33/2.58  thf('17', plain,
% 2.33/2.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.33/2.58         (((X8) = (k1_xboole_0))
% 2.33/2.58          | ~ (r1_tarski @ X8 @ X9)
% 2.33/2.58          | ~ (r1_tarski @ X8 @ X10)
% 2.33/2.58          | ~ (r1_xboole_0 @ X9 @ X10))),
% 2.33/2.58      inference('cnf', [status(esa)], [t67_xboole_1])).
% 2.33/2.58  thf('18', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i]:
% 2.33/2.58         (~ (r1_xboole_0 @ X0 @ X1)
% 2.33/2.58          | ~ (r1_tarski @ X0 @ X1)
% 2.33/2.58          | ((X0) = (k1_xboole_0)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['16', '17'])).
% 2.33/2.58  thf('19', plain,
% 2.33/2.58      (((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.33/2.58         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 2.33/2.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['15', '18'])).
% 2.33/2.58  thf('20', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(t44_tops_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.33/2.58  thf('21', plain,
% 2.33/2.58      (![X44 : $i, X45 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 2.33/2.58          | (r1_tarski @ (k1_tops_1 @ X45 @ X44) @ X44)
% 2.33/2.58          | ~ (l1_pre_topc @ X45))),
% 2.33/2.58      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.33/2.58  thf('22', plain,
% 2.33/2.58      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.33/2.58      inference('sup-', [status(thm)], ['20', '21'])).
% 2.33/2.58  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('24', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.33/2.58      inference('demod', [status(thm)], ['22', '23'])).
% 2.33/2.58  thf('25', plain,
% 2.33/2.58      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 2.33/2.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('demod', [status(thm)], ['19', '24'])).
% 2.33/2.58  thf('26', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(t84_tops_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( ( v2_tops_1 @ B @ A ) <=>
% 2.33/2.58             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.33/2.58  thf('27', plain,
% 2.33/2.58      (![X52 : $i, X53 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 2.33/2.58          | ((k1_tops_1 @ X53 @ X52) != (k1_xboole_0))
% 2.33/2.58          | (v2_tops_1 @ X52 @ X53)
% 2.33/2.58          | ~ (l1_pre_topc @ X53))),
% 2.33/2.58      inference('cnf', [status(esa)], [t84_tops_1])).
% 2.33/2.58  thf('28', plain,
% 2.33/2.58      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.58        | (v2_tops_1 @ sk_B @ sk_A)
% 2.33/2.58        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['26', '27'])).
% 2.33/2.58  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('30', plain,
% 2.33/2.58      (((v2_tops_1 @ sk_B @ sk_A)
% 2.33/2.58        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 2.33/2.58      inference('demod', [status(thm)], ['28', '29'])).
% 2.33/2.58  thf('31', plain,
% 2.33/2.58      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 2.33/2.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['25', '30'])).
% 2.33/2.58  thf('32', plain,
% 2.33/2.58      (((v2_tops_1 @ sk_B @ sk_A))
% 2.33/2.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('simplify', [status(thm)], ['31'])).
% 2.33/2.58  thf('33', plain,
% 2.33/2.58      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.58      inference('split', [status(esa)], ['0'])).
% 2.33/2.58  thf('34', plain,
% 2.33/2.58      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 2.33/2.58       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['32', '33'])).
% 2.33/2.58  thf('35', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.58      inference('sat_resolution*', [status(thm)], ['2', '34'])).
% 2.33/2.58  thf('36', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.58      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 2.33/2.58  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.33/2.58      inference('simplify', [status(thm)], ['10'])).
% 2.33/2.58  thf('38', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(dt_k2_tops_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( ( l1_pre_topc @ A ) & 
% 2.33/2.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.33/2.58       ( m1_subset_1 @
% 2.33/2.58         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.33/2.58  thf('39', plain,
% 2.33/2.58      (![X42 : $i, X43 : $i]:
% 2.33/2.58         (~ (l1_pre_topc @ X42)
% 2.33/2.58          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 2.33/2.58          | (m1_subset_1 @ (k2_tops_1 @ X42 @ X43) @ 
% 2.33/2.58             (k1_zfmisc_1 @ (u1_struct_0 @ X42))))),
% 2.33/2.58      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.33/2.58  thf('40', plain,
% 2.33/2.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.33/2.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.33/2.58        | ~ (l1_pre_topc @ sk_A))),
% 2.33/2.58      inference('sup-', [status(thm)], ['38', '39'])).
% 2.33/2.58  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('42', plain,
% 2.33/2.58      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('demod', [status(thm)], ['40', '41'])).
% 2.33/2.58  thf(dt_k3_subset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.33/2.58  thf('43', plain,
% 2.33/2.58      (![X17 : $i, X18 : $i]:
% 2.33/2.58         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 2.33/2.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.33/2.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.33/2.58  thf('44', plain,
% 2.33/2.58      ((m1_subset_1 @ 
% 2.33/2.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['42', '43'])).
% 2.33/2.58  thf(t44_subset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.58       ( ![C:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.58           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 2.33/2.58             ( r1_tarski @ B @ C ) ) ) ) ))).
% 2.33/2.58  thf('45', plain,
% 2.33/2.58      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 2.33/2.58          | ~ (r1_tarski @ X29 @ X27)
% 2.33/2.58          | (r1_xboole_0 @ X29 @ (k3_subset_1 @ X28 @ X27))
% 2.33/2.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 2.33/2.58      inference('cnf', [status(esa)], [t44_subset_1])).
% 2.33/2.58  thf('46', plain,
% 2.33/2.58      (![X0 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.33/2.58          | (r1_xboole_0 @ X0 @ 
% 2.33/2.58             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))
% 2.33/2.58          | ~ (r1_tarski @ X0 @ 
% 2.33/2.58               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['44', '45'])).
% 2.33/2.58  thf('47', plain,
% 2.33/2.58      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('demod', [status(thm)], ['40', '41'])).
% 2.33/2.58  thf(involutiveness_k3_subset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.33/2.58  thf('48', plain,
% 2.33/2.58      (![X19 : $i, X20 : $i]:
% 2.33/2.58         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 2.33/2.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 2.33/2.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.33/2.58  thf('49', plain,
% 2.33/2.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.33/2.58         = (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.58      inference('sup-', [status(thm)], ['47', '48'])).
% 2.33/2.58  thf('50', plain,
% 2.33/2.58      (![X0 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.33/2.58          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 2.33/2.58          | ~ (r1_tarski @ X0 @ 
% 2.33/2.58               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.58      inference('demod', [status(thm)], ['46', '49'])).
% 2.33/2.58  thf('51', plain,
% 2.33/2.58      (((r1_xboole_0 @ 
% 2.33/2.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.58         (k2_tops_1 @ sk_A @ sk_B))
% 2.33/2.58        | ~ (m1_subset_1 @ 
% 2.33/2.58             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['37', '50'])).
% 2.33/2.58  thf('52', plain,
% 2.33/2.58      ((m1_subset_1 @ 
% 2.33/2.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['42', '43'])).
% 2.33/2.58  thf('53', plain,
% 2.33/2.58      ((r1_xboole_0 @ 
% 2.33/2.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.58        (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.58      inference('demod', [status(thm)], ['51', '52'])).
% 2.33/2.58  thf('54', plain,
% 2.33/2.58      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('demod', [status(thm)], ['40', '41'])).
% 2.33/2.58  thf('55', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('56', plain,
% 2.33/2.58      (![X17 : $i, X18 : $i]:
% 2.33/2.58         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 2.33/2.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.33/2.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.33/2.58  thf('57', plain,
% 2.33/2.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['55', '56'])).
% 2.33/2.58  thf(redefinition_k4_subset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i,C:$i]:
% 2.33/2.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.33/2.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.33/2.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.33/2.58  thf('58', plain,
% 2.33/2.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 2.33/2.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 2.33/2.58          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 2.33/2.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.33/2.58  thf('59', plain,
% 2.33/2.58      (![X0 : $i]:
% 2.33/2.58         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 2.33/2.58            = (k2_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0))
% 2.33/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['57', '58'])).
% 2.33/2.58  thf('60', plain,
% 2.33/2.58      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58         (k2_tops_1 @ sk_A @ sk_B))
% 2.33/2.58         = (k2_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['54', '59'])).
% 2.33/2.58  thf('61', plain,
% 2.33/2.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['55', '56'])).
% 2.33/2.58  thf(t65_tops_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( ( k2_pre_topc @ A @ B ) =
% 2.33/2.58             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.33/2.58  thf('62', plain,
% 2.33/2.58      (![X48 : $i, X49 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 2.33/2.58          | ((k2_pre_topc @ X49 @ X48)
% 2.33/2.58              = (k4_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 2.33/2.58                 (k2_tops_1 @ X49 @ X48)))
% 2.33/2.58          | ~ (l1_pre_topc @ X49))),
% 2.33/2.58      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.33/2.58  thf('63', plain,
% 2.33/2.58      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.58        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.58            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['61', '62'])).
% 2.33/2.58  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('65', plain,
% 2.33/2.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['55', '56'])).
% 2.33/2.58  thf(t62_tops_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( ( k2_tops_1 @ A @ B ) =
% 2.33/2.58             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 2.33/2.58  thf('66', plain,
% 2.33/2.58      (![X46 : $i, X47 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 2.33/2.58          | ((k2_tops_1 @ X47 @ X46)
% 2.33/2.58              = (k2_tops_1 @ X47 @ (k3_subset_1 @ (u1_struct_0 @ X47) @ X46)))
% 2.33/2.58          | ~ (l1_pre_topc @ X47))),
% 2.33/2.58      inference('cnf', [status(esa)], [t62_tops_1])).
% 2.33/2.58  thf('67', plain,
% 2.33/2.58      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.58        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.58            = (k2_tops_1 @ sk_A @ 
% 2.33/2.58               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['65', '66'])).
% 2.33/2.58  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('69', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('70', plain,
% 2.33/2.58      (![X19 : $i, X20 : $i]:
% 2.33/2.58         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 2.33/2.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 2.33/2.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.33/2.58  thf('71', plain,
% 2.33/2.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 2.33/2.58      inference('sup-', [status(thm)], ['69', '70'])).
% 2.33/2.58  thf('72', plain,
% 2.33/2.58      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.58         = (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.58      inference('demod', [status(thm)], ['67', '68', '71'])).
% 2.33/2.58  thf('73', plain,
% 2.33/2.58      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.58            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.58      inference('demod', [status(thm)], ['63', '64', '72'])).
% 2.33/2.58  thf('74', plain,
% 2.33/2.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['55', '56'])).
% 2.33/2.58  thf(d3_tops_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( ( v1_tops_1 @ B @ A ) <=>
% 2.33/2.58             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 2.33/2.58  thf('75', plain,
% 2.33/2.58      (![X38 : $i, X39 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 2.33/2.58          | ~ (v1_tops_1 @ X38 @ X39)
% 2.33/2.58          | ((k2_pre_topc @ X39 @ X38) = (k2_struct_0 @ X39))
% 2.33/2.58          | ~ (l1_pre_topc @ X39))),
% 2.33/2.58      inference('cnf', [status(esa)], [d3_tops_1])).
% 2.33/2.58  thf('76', plain,
% 2.33/2.58      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.58        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.58            = (k2_struct_0 @ sk_A))
% 2.33/2.58        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 2.33/2.58      inference('sup-', [status(thm)], ['74', '75'])).
% 2.33/2.58  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('78', plain,
% 2.33/2.58      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.58          = (k2_struct_0 @ sk_A))
% 2.33/2.58        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 2.33/2.58      inference('demod', [status(thm)], ['76', '77'])).
% 2.33/2.58  thf('79', plain,
% 2.33/2.58      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.58      inference('split', [status(esa)], ['8'])).
% 2.33/2.58  thf('80', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(d4_tops_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( l1_pre_topc @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.58           ( ( v2_tops_1 @ B @ A ) <=>
% 2.33/2.58             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 2.33/2.58  thf('81', plain,
% 2.33/2.58      (![X40 : $i, X41 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 2.33/2.58          | ~ (v2_tops_1 @ X40 @ X41)
% 2.33/2.58          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X41) @ X40) @ X41)
% 2.33/2.58          | ~ (l1_pre_topc @ X41))),
% 2.33/2.58      inference('cnf', [status(esa)], [d4_tops_1])).
% 2.33/2.58  thf('82', plain,
% 2.33/2.58      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.58        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.33/2.58        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.58      inference('sup-', [status(thm)], ['80', '81'])).
% 2.33/2.58  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('84', plain,
% 2.33/2.58      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.33/2.58        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.58      inference('demod', [status(thm)], ['82', '83'])).
% 2.33/2.58  thf('85', plain,
% 2.33/2.58      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 2.33/2.58         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['79', '84'])).
% 2.33/2.58  thf('86', plain,
% 2.33/2.58      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 2.33/2.58       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.58      inference('split', [status(esa)], ['8'])).
% 2.33/2.58  thf('87', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.59      inference('sat_resolution*', [status(thm)], ['2', '34', '86'])).
% 2.33/2.59  thf('88', plain,
% 2.33/2.59      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 2.33/2.59      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 2.33/2.59  thf('89', plain,
% 2.33/2.59      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.59         = (k2_struct_0 @ sk_A))),
% 2.33/2.59      inference('demod', [status(thm)], ['78', '88'])).
% 2.33/2.59  thf('90', plain,
% 2.33/2.59      (((k2_struct_0 @ sk_A)
% 2.33/2.59         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.59            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.59            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.59      inference('demod', [status(thm)], ['73', '89'])).
% 2.33/2.59  thf('91', plain,
% 2.33/2.59      (((k2_struct_0 @ sk_A)
% 2.33/2.59         = (k2_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.59            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.59      inference('sup+', [status(thm)], ['60', '90'])).
% 2.33/2.59  thf(t73_xboole_1, axiom,
% 2.33/2.59    (![A:$i,B:$i,C:$i]:
% 2.33/2.59     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.33/2.59       ( r1_tarski @ A @ B ) ))).
% 2.33/2.59  thf('92', plain,
% 2.33/2.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.33/2.59         ((r1_tarski @ X11 @ X12)
% 2.33/2.59          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 2.33/2.59          | ~ (r1_xboole_0 @ X11 @ X13))),
% 2.33/2.59      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.33/2.59  thf('93', plain,
% 2.33/2.59      (![X0 : $i]:
% 2.33/2.59         (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_A))
% 2.33/2.59          | ~ (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 2.33/2.59          | (r1_tarski @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['91', '92'])).
% 2.33/2.59  thf('94', plain,
% 2.33/2.59      (((r1_tarski @ 
% 2.33/2.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.59        | ~ (r1_tarski @ 
% 2.33/2.59             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59             (k2_struct_0 @ sk_A)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['53', '93'])).
% 2.33/2.59  thf('95', plain,
% 2.33/2.59      ((m1_subset_1 @ 
% 2.33/2.59        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['42', '43'])).
% 2.33/2.59  thf('96', plain,
% 2.33/2.59      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['55', '56'])).
% 2.33/2.59  thf(dt_k2_pre_topc, axiom,
% 2.33/2.59    (![A:$i,B:$i]:
% 2.33/2.59     ( ( ( l1_pre_topc @ A ) & 
% 2.33/2.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.33/2.59       ( m1_subset_1 @
% 2.33/2.59         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.33/2.59  thf('97', plain,
% 2.33/2.59      (![X34 : $i, X35 : $i]:
% 2.33/2.59         (~ (l1_pre_topc @ X34)
% 2.33/2.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.33/2.59          | (m1_subset_1 @ (k2_pre_topc @ X34 @ X35) @ 
% 2.33/2.59             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 2.33/2.59      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.33/2.59  thf('98', plain,
% 2.33/2.59      (((m1_subset_1 @ 
% 2.33/2.59         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 2.33/2.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.33/2.59        | ~ (l1_pre_topc @ sk_A))),
% 2.33/2.59      inference('sup-', [status(thm)], ['96', '97'])).
% 2.33/2.59  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.59  thf('100', plain,
% 2.33/2.59      ((m1_subset_1 @ 
% 2.33/2.59        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 2.33/2.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('demod', [status(thm)], ['98', '99'])).
% 2.33/2.59  thf('101', plain,
% 2.33/2.59      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.59         = (k2_struct_0 @ sk_A))),
% 2.33/2.59      inference('demod', [status(thm)], ['78', '88'])).
% 2.33/2.59  thf('102', plain,
% 2.33/2.59      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('demod', [status(thm)], ['100', '101'])).
% 2.33/2.59  thf('103', plain,
% 2.33/2.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.33/2.59         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 2.33/2.59          | ~ (r1_xboole_0 @ X29 @ (k3_subset_1 @ X28 @ X27))
% 2.33/2.59          | (r1_tarski @ X29 @ X27)
% 2.33/2.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 2.33/2.59      inference('cnf', [status(esa)], [t44_subset_1])).
% 2.33/2.59  thf('104', plain,
% 2.33/2.59      (![X0 : $i]:
% 2.33/2.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.33/2.59          | (r1_tarski @ X0 @ (k2_struct_0 @ sk_A))
% 2.33/2.59          | ~ (r1_xboole_0 @ X0 @ 
% 2.33/2.59               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))),
% 2.33/2.59      inference('sup-', [status(thm)], ['102', '103'])).
% 2.33/2.59  thf('105', plain,
% 2.33/2.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.59  thf(d1_tops_1, axiom,
% 2.33/2.59    (![A:$i]:
% 2.33/2.59     ( ( l1_pre_topc @ A ) =>
% 2.33/2.59       ( ![B:$i]:
% 2.33/2.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.59           ( ( k1_tops_1 @ A @ B ) =
% 2.33/2.59             ( k3_subset_1 @
% 2.33/2.59               ( u1_struct_0 @ A ) @ 
% 2.33/2.59               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 2.33/2.59  thf('106', plain,
% 2.33/2.59      (![X36 : $i, X37 : $i]:
% 2.33/2.59         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.33/2.59          | ((k1_tops_1 @ X37 @ X36)
% 2.33/2.59              = (k3_subset_1 @ (u1_struct_0 @ X37) @ 
% 2.33/2.59                 (k2_pre_topc @ X37 @ (k3_subset_1 @ (u1_struct_0 @ X37) @ X36))))
% 2.33/2.59          | ~ (l1_pre_topc @ X37))),
% 2.33/2.59      inference('cnf', [status(esa)], [d1_tops_1])).
% 2.33/2.59  thf('107', plain,
% 2.33/2.59      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.59        | ((k1_tops_1 @ sk_A @ sk_B)
% 2.33/2.59            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.59               (k2_pre_topc @ sk_A @ 
% 2.33/2.59                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.33/2.59      inference('sup-', [status(thm)], ['105', '106'])).
% 2.33/2.59  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.59  thf('109', plain,
% 2.33/2.59      (((k1_tops_1 @ sk_A @ sk_B)
% 2.33/2.59         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.59            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.33/2.59      inference('demod', [status(thm)], ['107', '108'])).
% 2.33/2.59  thf('110', plain,
% 2.33/2.59      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.59      inference('split', [status(esa)], ['8'])).
% 2.33/2.59  thf('111', plain,
% 2.33/2.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.59  thf('112', plain,
% 2.33/2.59      (![X52 : $i, X53 : $i]:
% 2.33/2.59         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 2.33/2.59          | ~ (v2_tops_1 @ X52 @ X53)
% 2.33/2.59          | ((k1_tops_1 @ X53 @ X52) = (k1_xboole_0))
% 2.33/2.59          | ~ (l1_pre_topc @ X53))),
% 2.33/2.59      inference('cnf', [status(esa)], [t84_tops_1])).
% 2.33/2.59  thf('113', plain,
% 2.33/2.59      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.59        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.33/2.59        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.59      inference('sup-', [status(thm)], ['111', '112'])).
% 2.33/2.59  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.59  thf('115', plain,
% 2.33/2.59      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.33/2.59        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.59      inference('demod', [status(thm)], ['113', '114'])).
% 2.33/2.59  thf('116', plain,
% 2.33/2.59      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 2.33/2.59         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['110', '115'])).
% 2.33/2.59  thf('117', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.59      inference('sat_resolution*', [status(thm)], ['2', '34', '86'])).
% 2.33/2.59  thf('118', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 2.33/2.59      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 2.33/2.59  thf('119', plain,
% 2.33/2.59      (((k1_xboole_0)
% 2.33/2.59         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.59            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.33/2.59      inference('demod', [status(thm)], ['109', '118'])).
% 2.33/2.59  thf('120', plain,
% 2.33/2.59      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.59         = (k2_struct_0 @ sk_A))),
% 2.33/2.59      inference('demod', [status(thm)], ['78', '88'])).
% 2.33/2.59  thf('121', plain,
% 2.33/2.59      (((k1_xboole_0)
% 2.33/2.59         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 2.33/2.59      inference('demod', [status(thm)], ['119', '120'])).
% 2.33/2.59  thf('122', plain,
% 2.33/2.59      (![X0 : $i]:
% 2.33/2.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.33/2.59          | (r1_tarski @ X0 @ (k2_struct_0 @ sk_A))
% 2.33/2.59          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.33/2.59      inference('demod', [status(thm)], ['104', '121'])).
% 2.33/2.59  thf('123', plain,
% 2.33/2.59      ((~ (r1_xboole_0 @ 
% 2.33/2.59           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59           k1_xboole_0)
% 2.33/2.59        | (r1_tarski @ 
% 2.33/2.59           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59           (k2_struct_0 @ sk_A)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['95', '122'])).
% 2.33/2.59  thf('124', plain,
% 2.33/2.59      ((r1_xboole_0 @ 
% 2.33/2.59        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59        (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.59      inference('demod', [status(thm)], ['51', '52'])).
% 2.33/2.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.33/2.59  thf('125', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.33/2.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.33/2.59  thf('126', plain,
% 2.33/2.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.59         (~ (r1_xboole_0 @ X0 @ X1)
% 2.33/2.59          | ~ (r1_tarski @ X2 @ X1)
% 2.33/2.59          | (r1_xboole_0 @ X0 @ X2))),
% 2.33/2.59      inference('sup-', [status(thm)], ['11', '12'])).
% 2.33/2.59  thf('127', plain,
% 2.33/2.59      (![X0 : $i, X1 : $i]:
% 2.33/2.59         ((r1_xboole_0 @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.33/2.59      inference('sup-', [status(thm)], ['125', '126'])).
% 2.33/2.59  thf('128', plain,
% 2.33/2.59      ((r1_xboole_0 @ 
% 2.33/2.59        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59        k1_xboole_0)),
% 2.33/2.59      inference('sup-', [status(thm)], ['124', '127'])).
% 2.33/2.59  thf('129', plain,
% 2.33/2.59      ((r1_tarski @ 
% 2.33/2.59        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59        (k2_struct_0 @ sk_A))),
% 2.33/2.59      inference('demod', [status(thm)], ['123', '128'])).
% 2.33/2.59  thf('130', plain,
% 2.33/2.59      ((r1_tarski @ 
% 2.33/2.59        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.59      inference('demod', [status(thm)], ['94', '129'])).
% 2.33/2.59  thf('131', plain,
% 2.33/2.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.59  thf(t35_subset_1, axiom,
% 2.33/2.59    (![A:$i,B:$i]:
% 2.33/2.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.59       ( ![C:$i]:
% 2.33/2.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.59           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 2.33/2.59             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.33/2.59  thf('132', plain,
% 2.33/2.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.33/2.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 2.33/2.59          | (r1_tarski @ X24 @ (k3_subset_1 @ X25 @ X26))
% 2.33/2.59          | ~ (r1_tarski @ X26 @ (k3_subset_1 @ X25 @ X24))
% 2.33/2.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 2.33/2.59      inference('cnf', [status(esa)], [t35_subset_1])).
% 2.33/2.59  thf('133', plain,
% 2.33/2.59      (![X0 : $i]:
% 2.33/2.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.33/2.59          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.33/2.59          | (r1_tarski @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['131', '132'])).
% 2.33/2.59  thf('134', plain,
% 2.33/2.59      (((r1_tarski @ sk_B @ 
% 2.33/2.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.59          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))
% 2.33/2.59        | ~ (m1_subset_1 @ 
% 2.33/2.59             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.33/2.59      inference('sup-', [status(thm)], ['130', '133'])).
% 2.33/2.59  thf('135', plain,
% 2.33/2.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.33/2.59         = (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.59      inference('sup-', [status(thm)], ['47', '48'])).
% 2.33/2.59  thf('136', plain,
% 2.33/2.59      ((m1_subset_1 @ 
% 2.33/2.59        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.33/2.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.59      inference('sup-', [status(thm)], ['42', '43'])).
% 2.33/2.59  thf('137', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.59      inference('demod', [status(thm)], ['134', '135', '136'])).
% 2.33/2.59  thf('138', plain, ($false), inference('demod', [status(thm)], ['36', '137'])).
% 2.33/2.59  
% 2.33/2.59  % SZS output end Refutation
% 2.33/2.59  
% 2.33/2.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
