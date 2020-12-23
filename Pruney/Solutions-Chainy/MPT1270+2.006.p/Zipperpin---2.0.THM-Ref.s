%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p5NOFJ2p9e

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:26 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 212 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  752 (2062 expanded)
%              Number of equality atoms :   44 (  80 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('3',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( k2_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ X20 @ ( k2_pre_topc @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_tops_1 @ X23 @ X22 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k2_pre_topc @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tops_1 @ X26 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('59',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','38','58'])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('62',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('68',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('69',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','60','67','68'])).

thf('70',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['40','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p5NOFJ2p9e
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 487 iterations in 0.149s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.60  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.41/0.60  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.41/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.41/0.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(t88_tops_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.60             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( l1_pre_topc @ A ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60              ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.60                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.60         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.41/0.60       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.60        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf(t12_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.60          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf(t41_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.60       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.41/0.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.60  thf(t36_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.41/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.60          (k4_xboole_0 @ X2 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.41/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.41/0.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.60  thf(t38_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.41/0.60       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i]:
% 0.41/0.60         (((X9) = (k1_xboole_0))
% 0.41/0.60          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.41/0.60          | ((X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 0.41/0.60          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['14', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.41/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['6', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t74_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( k1_tops_1 @ A @ B ) =
% 0.41/0.60             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.60          | ((k1_tops_1 @ X25 @ X24)
% 0.41/0.60              = (k7_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 0.41/0.60                 (k2_tops_1 @ X25 @ X24)))
% 0.41/0.60          | ~ (l1_pre_topc @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.41/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k7_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.41/0.60          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (((k1_tops_1 @ sk_A @ sk_B)
% 0.41/0.60         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.41/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['20', '28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t84_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.60             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.60          | ((k1_tops_1 @ X27 @ X26) != (k1_xboole_0))
% 0.41/0.60          | (v2_tops_1 @ X26 @ X27)
% 0.41/0.60          | ~ (l1_pre_topc @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v2_tops_1 @ sk_B @ sk_A)
% 0.41/0.60        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (((v2_tops_1 @ sk_B @ sk_A)
% 0.41/0.60        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.41/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (((v2_tops_1 @ sk_B @ sk_A))
% 0.41/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.41/0.60       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf('39', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.41/0.60  thf('40', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t48_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.60          | (r1_tarski @ X20 @ (k2_pre_topc @ X21 @ X20))
% 0.41/0.60          | ~ (l1_pre_topc @ X21))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('45', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(l78_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.60             ( k7_subset_1 @
% 0.41/0.60               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.41/0.60               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X22 : $i, X23 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60          | ((k2_tops_1 @ X23 @ X22)
% 0.41/0.60              = (k7_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.41/0.60                 (k2_pre_topc @ X23 @ X22) @ (k1_tops_1 @ X23 @ X22)))
% 0.41/0.60          | ~ (l1_pre_topc @ X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.60          | ~ (v2_tops_1 @ X26 @ X27)
% 0.41/0.60          | ((k1_tops_1 @ X27 @ X26) = (k1_xboole_0))
% 0.41/0.60          | ~ (l1_pre_topc @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.60  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['54', '55'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.41/0.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['51', '56'])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.41/0.60       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('59', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['2', '38', '58'])).
% 0.41/0.60  thf('60', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_k2_pre_topc, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60       ( m1_subset_1 @
% 0.41/0.60         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X18)
% 0.41/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.60          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.41/0.60  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.41/0.60          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.41/0.60  thf(t3_boole, axiom,
% 0.41/0.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.60  thf('68', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.41/0.60  thf('69', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['50', '60', '67', '68'])).
% 0.41/0.60  thf('70', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['45', '69'])).
% 0.41/0.60  thf('71', plain, ($false), inference('demod', [status(thm)], ['40', '70'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
