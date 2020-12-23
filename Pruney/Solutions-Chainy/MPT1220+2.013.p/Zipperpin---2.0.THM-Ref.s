%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fNnKBmdg9d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:41 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 227 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  570 (1371 expanded)
%              Number of equality atoms :   46 ( 137 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_struct_0 @ X22 ) ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
       != ( k2_subset_1 @ X13 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X13 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('9',plain,(
    ! [X13: $i] :
      ( ~ ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X13 @ ( k2_subset_1 @ X13 ) ) @ ( k2_subset_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('13',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('25',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(demod,[status(thm)],['9','10','13','14','23','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','31'])).

thf('34',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('40',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','31'])).

thf('43',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ X23 @ ( k2_pre_topc @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t27_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tops_1])).

thf('53',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fNnKBmdg9d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:05:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 2.86/3.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.86/3.08  % Solved by: fo/fo7.sh
% 2.86/3.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.86/3.08  % done 2878 iterations in 2.595s
% 2.86/3.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.86/3.08  % SZS output start Refutation
% 2.86/3.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.86/3.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.86/3.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.86/3.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.86/3.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.86/3.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.86/3.08  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.86/3.08  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.86/3.08  thf(sk_A_type, type, sk_A: $i).
% 2.86/3.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.86/3.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.86/3.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.86/3.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.86/3.08  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 2.86/3.08  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.86/3.08  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.86/3.08  thf(fc3_struct_0, axiom,
% 2.86/3.08    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 2.86/3.08  thf('0', plain,
% 2.86/3.08      (![X21 : $i]:
% 2.86/3.08         ((v1_xboole_0 @ (k1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.86/3.08      inference('cnf', [status(esa)], [fc3_struct_0])).
% 2.86/3.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.86/3.08  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.86/3.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.86/3.08  thf(t8_boole, axiom,
% 2.86/3.08    (![A:$i,B:$i]:
% 2.86/3.08     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.86/3.08  thf('2', plain,
% 2.86/3.08      (![X7 : $i, X8 : $i]:
% 2.86/3.08         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 2.86/3.08      inference('cnf', [status(esa)], [t8_boole])).
% 2.86/3.08  thf('3', plain,
% 2.86/3.08      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.08      inference('sup-', [status(thm)], ['1', '2'])).
% 2.86/3.08  thf('4', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 2.86/3.08      inference('sup-', [status(thm)], ['0', '3'])).
% 2.86/3.08  thf(t27_pre_topc, axiom,
% 2.86/3.08    (![A:$i]:
% 2.86/3.08     ( ( l1_struct_0 @ A ) =>
% 2.86/3.08       ( ( k2_struct_0 @ A ) =
% 2.86/3.08         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 2.86/3.08  thf('5', plain,
% 2.86/3.08      (![X22 : $i]:
% 2.86/3.08         (((k2_struct_0 @ X22)
% 2.86/3.08            = (k3_subset_1 @ (u1_struct_0 @ X22) @ (k1_struct_0 @ X22)))
% 2.86/3.08          | ~ (l1_struct_0 @ X22))),
% 2.86/3.08      inference('cnf', [status(esa)], [t27_pre_topc])).
% 2.86/3.08  thf('6', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (((k2_struct_0 @ X0)
% 2.86/3.08            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 2.86/3.08          | ~ (l1_struct_0 @ X0)
% 2.86/3.08          | ~ (l1_struct_0 @ X0))),
% 2.86/3.08      inference('sup+', [status(thm)], ['4', '5'])).
% 2.86/3.08  thf('7', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_struct_0 @ X0)
% 2.86/3.08          | ((k2_struct_0 @ X0)
% 2.86/3.08              = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0)))),
% 2.86/3.08      inference('simplify', [status(thm)], ['6'])).
% 2.86/3.08  thf(t39_subset_1, axiom,
% 2.86/3.08    (![A:$i,B:$i]:
% 2.86/3.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.86/3.08       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 2.86/3.08         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 2.86/3.08  thf('8', plain,
% 2.86/3.08      (![X13 : $i, X14 : $i]:
% 2.86/3.08         (((X14) != (k2_subset_1 @ X13))
% 2.86/3.08          | (r1_tarski @ (k3_subset_1 @ X13 @ X14) @ X14)
% 2.86/3.08          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 2.86/3.08      inference('cnf', [status(esa)], [t39_subset_1])).
% 2.86/3.08  thf('9', plain,
% 2.86/3.08      (![X13 : $i]:
% 2.86/3.08         (~ (m1_subset_1 @ (k2_subset_1 @ X13) @ (k1_zfmisc_1 @ X13))
% 2.86/3.08          | (r1_tarski @ (k3_subset_1 @ X13 @ (k2_subset_1 @ X13)) @ 
% 2.86/3.08             (k2_subset_1 @ X13)))),
% 2.86/3.08      inference('simplify', [status(thm)], ['8'])).
% 2.86/3.08  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.86/3.08  thf('10', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 2.86/3.08      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.86/3.08  thf(dt_k2_subset_1, axiom,
% 2.86/3.08    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.86/3.08  thf('11', plain,
% 2.86/3.08      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 2.86/3.08      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.86/3.08  thf('12', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 2.86/3.08      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.86/3.08  thf('13', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 2.86/3.08      inference('demod', [status(thm)], ['11', '12'])).
% 2.86/3.08  thf('14', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 2.86/3.08      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.86/3.08  thf('15', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 2.86/3.08      inference('demod', [status(thm)], ['11', '12'])).
% 2.86/3.08  thf(d5_subset_1, axiom,
% 2.86/3.08    (![A:$i,B:$i]:
% 2.86/3.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.86/3.08       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.86/3.08  thf('16', plain,
% 2.86/3.08      (![X10 : $i, X11 : $i]:
% 2.86/3.08         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 2.86/3.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 2.86/3.08      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.86/3.08  thf('17', plain,
% 2.86/3.08      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.86/3.08      inference('sup-', [status(thm)], ['15', '16'])).
% 2.86/3.08  thf(t3_boole, axiom,
% 2.86/3.08    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.86/3.08  thf('18', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 2.86/3.08      inference('cnf', [status(esa)], [t3_boole])).
% 2.86/3.08  thf(t48_xboole_1, axiom,
% 2.86/3.08    (![A:$i,B:$i]:
% 2.86/3.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.86/3.08  thf('19', plain,
% 2.86/3.08      (![X5 : $i, X6 : $i]:
% 2.86/3.08         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 2.86/3.08           = (k3_xboole_0 @ X5 @ X6))),
% 2.86/3.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.86/3.08  thf('20', plain,
% 2.86/3.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.86/3.08      inference('sup+', [status(thm)], ['18', '19'])).
% 2.86/3.08  thf(t2_boole, axiom,
% 2.86/3.08    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.86/3.08  thf('21', plain,
% 2.86/3.08      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.86/3.08      inference('cnf', [status(esa)], [t2_boole])).
% 2.86/3.08  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.86/3.08      inference('demod', [status(thm)], ['20', '21'])).
% 2.86/3.08  thf('23', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 2.86/3.08      inference('demod', [status(thm)], ['17', '22'])).
% 2.86/3.08  thf('24', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 2.86/3.08      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.86/3.08  thf('25', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 2.86/3.08      inference('demod', [status(thm)], ['9', '10', '13', '14', '23', '24'])).
% 2.86/3.08  thf(t3_subset, axiom,
% 2.86/3.08    (![A:$i,B:$i]:
% 2.86/3.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.86/3.08  thf('26', plain,
% 2.86/3.08      (![X15 : $i, X17 : $i]:
% 2.86/3.08         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.86/3.08      inference('cnf', [status(esa)], [t3_subset])).
% 2.86/3.08  thf('27', plain,
% 2.86/3.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.86/3.08      inference('sup-', [status(thm)], ['25', '26'])).
% 2.86/3.08  thf('28', plain,
% 2.86/3.08      (![X10 : $i, X11 : $i]:
% 2.86/3.08         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 2.86/3.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 2.86/3.08      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.86/3.08  thf('29', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 2.86/3.08      inference('sup-', [status(thm)], ['27', '28'])).
% 2.86/3.08  thf('30', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 2.86/3.08      inference('cnf', [status(esa)], [t3_boole])).
% 2.86/3.08  thf('31', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.86/3.08      inference('demod', [status(thm)], ['29', '30'])).
% 2.86/3.08  thf('32', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 2.86/3.08      inference('demod', [status(thm)], ['7', '31'])).
% 2.86/3.08  thf('33', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 2.86/3.08      inference('demod', [status(thm)], ['7', '31'])).
% 2.86/3.08  thf('34', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 2.86/3.08      inference('demod', [status(thm)], ['11', '12'])).
% 2.86/3.08  thf(dt_k2_pre_topc, axiom,
% 2.86/3.08    (![A:$i,B:$i]:
% 2.86/3.08     ( ( ( l1_pre_topc @ A ) & 
% 2.86/3.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.86/3.08       ( m1_subset_1 @
% 2.86/3.08         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.86/3.08  thf('35', plain,
% 2.86/3.08      (![X18 : $i, X19 : $i]:
% 2.86/3.08         (~ (l1_pre_topc @ X18)
% 2.86/3.08          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.86/3.08          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 2.86/3.08             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 2.86/3.08      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.86/3.08  thf('36', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.86/3.08           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.86/3.08          | ~ (l1_pre_topc @ X0))),
% 2.86/3.08      inference('sup-', [status(thm)], ['34', '35'])).
% 2.86/3.08  thf('37', plain,
% 2.86/3.08      (![X15 : $i, X16 : $i]:
% 2.86/3.08         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.86/3.08      inference('cnf', [status(esa)], [t3_subset])).
% 2.86/3.08  thf('38', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_pre_topc @ X0)
% 2.86/3.08          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.86/3.08             (u1_struct_0 @ X0)))),
% 2.86/3.08      inference('sup-', [status(thm)], ['36', '37'])).
% 2.86/3.08  thf('39', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         ((r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 2.86/3.08           (u1_struct_0 @ X0))
% 2.86/3.08          | ~ (l1_struct_0 @ X0)
% 2.86/3.08          | ~ (l1_pre_topc @ X0))),
% 2.86/3.08      inference('sup+', [status(thm)], ['33', '38'])).
% 2.86/3.08  thf(dt_l1_pre_topc, axiom,
% 2.86/3.08    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.86/3.08  thf('40', plain,
% 2.86/3.08      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 2.86/3.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.86/3.08  thf('41', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_pre_topc @ X0)
% 2.86/3.08          | (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 2.86/3.08             (u1_struct_0 @ X0)))),
% 2.86/3.08      inference('clc', [status(thm)], ['39', '40'])).
% 2.86/3.08  thf('42', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 2.86/3.08      inference('demod', [status(thm)], ['7', '31'])).
% 2.86/3.08  thf('43', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 2.86/3.08      inference('demod', [status(thm)], ['11', '12'])).
% 2.86/3.08  thf(t48_pre_topc, axiom,
% 2.86/3.08    (![A:$i]:
% 2.86/3.08     ( ( l1_pre_topc @ A ) =>
% 2.86/3.08       ( ![B:$i]:
% 2.86/3.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.86/3.08           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 2.86/3.08  thf('44', plain,
% 2.86/3.08      (![X23 : $i, X24 : $i]:
% 2.86/3.08         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.86/3.08          | (r1_tarski @ X23 @ (k2_pre_topc @ X24 @ X23))
% 2.86/3.08          | ~ (l1_pre_topc @ X24))),
% 2.86/3.08      inference('cnf', [status(esa)], [t48_pre_topc])).
% 2.86/3.08  thf('45', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_pre_topc @ X0)
% 2.86/3.08          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 2.86/3.08             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 2.86/3.08      inference('sup-', [status(thm)], ['43', '44'])).
% 2.86/3.08  thf('46', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 2.86/3.08           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 2.86/3.08          | ~ (l1_struct_0 @ X0)
% 2.86/3.08          | ~ (l1_pre_topc @ X0))),
% 2.86/3.08      inference('sup+', [status(thm)], ['42', '45'])).
% 2.86/3.08  thf('47', plain,
% 2.86/3.08      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 2.86/3.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.86/3.08  thf('48', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_pre_topc @ X0)
% 2.86/3.08          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 2.86/3.08             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 2.86/3.08      inference('clc', [status(thm)], ['46', '47'])).
% 2.86/3.08  thf(d10_xboole_0, axiom,
% 2.86/3.08    (![A:$i,B:$i]:
% 2.86/3.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.86/3.08  thf('49', plain,
% 2.86/3.08      (![X0 : $i, X2 : $i]:
% 2.86/3.08         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.86/3.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.86/3.08  thf('50', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_pre_topc @ X0)
% 2.86/3.08          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 2.86/3.08               (u1_struct_0 @ X0))
% 2.86/3.08          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 2.86/3.08      inference('sup-', [status(thm)], ['48', '49'])).
% 2.86/3.08  thf('51', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (~ (l1_pre_topc @ X0)
% 2.86/3.08          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 2.86/3.08          | ~ (l1_pre_topc @ X0))),
% 2.86/3.08      inference('sup-', [status(thm)], ['41', '50'])).
% 2.86/3.08  thf('52', plain,
% 2.86/3.08      (![X0 : $i]:
% 2.86/3.08         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 2.86/3.08          | ~ (l1_pre_topc @ X0))),
% 2.86/3.08      inference('simplify', [status(thm)], ['51'])).
% 2.86/3.08  thf(t27_tops_1, conjecture,
% 2.86/3.08    (![A:$i]:
% 2.86/3.08     ( ( l1_pre_topc @ A ) =>
% 2.86/3.08       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 2.86/3.08  thf(zf_stmt_0, negated_conjecture,
% 2.86/3.08    (~( ![A:$i]:
% 2.86/3.08        ( ( l1_pre_topc @ A ) =>
% 2.86/3.08          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 2.86/3.08    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 2.86/3.08  thf('53', plain,
% 2.86/3.08      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 2.86/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.08  thf('54', plain,
% 2.86/3.08      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 2.86/3.08      inference('sup-', [status(thm)], ['52', '53'])).
% 2.86/3.08  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 2.86/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.08  thf('56', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 2.86/3.08      inference('demod', [status(thm)], ['54', '55'])).
% 2.86/3.08  thf('57', plain,
% 2.86/3.08      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 2.86/3.08      inference('sup-', [status(thm)], ['32', '56'])).
% 2.86/3.08  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 2.86/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.08  thf('59', plain,
% 2.86/3.08      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 2.86/3.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.86/3.08  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 2.86/3.08      inference('sup-', [status(thm)], ['58', '59'])).
% 2.86/3.08  thf('61', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 2.86/3.08      inference('demod', [status(thm)], ['57', '60'])).
% 2.86/3.08  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 2.86/3.08  
% 2.86/3.08  % SZS output end Refutation
% 2.86/3.08  
% 2.86/3.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
