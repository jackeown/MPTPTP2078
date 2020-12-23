%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XHXY2LcHXR

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:02 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 186 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  926 (2169 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X19 @ X18 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','52'])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( r1_tarski @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['57','76'])).

thf('78',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['12','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XHXY2LcHXR
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.67/2.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.67/2.84  % Solved by: fo/fo7.sh
% 2.67/2.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.67/2.84  % done 3174 iterations in 2.350s
% 2.67/2.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.67/2.84  % SZS output start Refutation
% 2.67/2.84  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.67/2.84  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.67/2.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.67/2.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.67/2.84  thf(sk_B_type, type, sk_B: $i).
% 2.67/2.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.67/2.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.67/2.84  thf(sk_A_type, type, sk_A: $i).
% 2.67/2.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.67/2.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.67/2.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.67/2.84  thf(sk_C_type, type, sk_C: $i).
% 2.67/2.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.67/2.84  thf(t50_tops_1, conjecture,
% 2.67/2.84    (![A:$i]:
% 2.67/2.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.67/2.84       ( ![B:$i]:
% 2.67/2.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.84           ( ![C:$i]:
% 2.67/2.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.84               ( r1_tarski @
% 2.67/2.84                 ( k1_tops_1 @
% 2.67/2.84                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 2.67/2.84                 ( k7_subset_1 @
% 2.67/2.84                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 2.67/2.84                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.67/2.84  thf(zf_stmt_0, negated_conjecture,
% 2.67/2.84    (~( ![A:$i]:
% 2.67/2.84        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.67/2.84          ( ![B:$i]:
% 2.67/2.84            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.84              ( ![C:$i]:
% 2.67/2.84                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.84                  ( r1_tarski @
% 2.67/2.84                    ( k1_tops_1 @
% 2.67/2.84                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 2.67/2.84                    ( k7_subset_1 @
% 2.67/2.84                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 2.67/2.84                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 2.67/2.84    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 2.67/2.84  thf('0', plain,
% 2.67/2.84      (~ (r1_tarski @ 
% 2.67/2.84          (k1_tops_1 @ sk_A @ 
% 2.67/2.84           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 2.67/2.84          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.67/2.84           (k1_tops_1 @ sk_A @ sk_C)))),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf('1', plain,
% 2.67/2.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf(redefinition_k7_subset_1, axiom,
% 2.67/2.84    (![A:$i,B:$i,C:$i]:
% 2.67/2.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.84       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.67/2.84  thf('2', plain,
% 2.67/2.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.67/2.84         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 2.67/2.84          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 2.67/2.84      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.67/2.84  thf('3', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.67/2.84           = (k4_xboole_0 @ sk_B @ X0))),
% 2.67/2.84      inference('sup-', [status(thm)], ['1', '2'])).
% 2.67/2.84  thf('4', plain,
% 2.67/2.84      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 2.67/2.84          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.67/2.84           (k1_tops_1 @ sk_A @ sk_C)))),
% 2.67/2.84      inference('demod', [status(thm)], ['0', '3'])).
% 2.67/2.84  thf('5', plain,
% 2.67/2.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf(dt_k1_tops_1, axiom,
% 2.67/2.84    (![A:$i,B:$i]:
% 2.67/2.84     ( ( ( l1_pre_topc @ A ) & 
% 2.67/2.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.67/2.84       ( m1_subset_1 @
% 2.67/2.84         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.67/2.84  thf('6', plain,
% 2.67/2.84      (![X24 : $i, X25 : $i]:
% 2.67/2.84         (~ (l1_pre_topc @ X24)
% 2.67/2.84          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.67/2.84          | (m1_subset_1 @ (k1_tops_1 @ X24 @ X25) @ 
% 2.67/2.84             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 2.67/2.84      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.67/2.84  thf('7', plain,
% 2.67/2.84      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.67/2.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.84        | ~ (l1_pre_topc @ sk_A))),
% 2.67/2.84      inference('sup-', [status(thm)], ['5', '6'])).
% 2.67/2.84  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf('9', plain,
% 2.67/2.84      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.67/2.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('demod', [status(thm)], ['7', '8'])).
% 2.67/2.84  thf('10', plain,
% 2.67/2.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.67/2.84         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 2.67/2.84          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 2.67/2.84      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.67/2.84  thf('11', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.67/2.84           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 2.67/2.84      inference('sup-', [status(thm)], ['9', '10'])).
% 2.67/2.84  thf('12', plain,
% 2.67/2.84      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 2.67/2.84          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 2.67/2.84      inference('demod', [status(thm)], ['4', '11'])).
% 2.67/2.84  thf('13', plain,
% 2.67/2.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf('14', plain,
% 2.67/2.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf(dt_k7_subset_1, axiom,
% 2.67/2.84    (![A:$i,B:$i,C:$i]:
% 2.67/2.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.84       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.67/2.84  thf('15', plain,
% 2.67/2.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.67/2.84         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.67/2.84          | (m1_subset_1 @ (k7_subset_1 @ X19 @ X18 @ X20) @ 
% 2.67/2.84             (k1_zfmisc_1 @ X19)))),
% 2.67/2.84      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 2.67/2.84  thf('16', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 2.67/2.84          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['14', '15'])).
% 2.67/2.84  thf('17', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.67/2.84           = (k4_xboole_0 @ sk_B @ X0))),
% 2.67/2.84      inference('sup-', [status(thm)], ['1', '2'])).
% 2.67/2.84  thf('18', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.67/2.84          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('demod', [status(thm)], ['16', '17'])).
% 2.67/2.84  thf(t48_tops_1, axiom,
% 2.67/2.84    (![A:$i]:
% 2.67/2.84     ( ( l1_pre_topc @ A ) =>
% 2.67/2.84       ( ![B:$i]:
% 2.67/2.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.84           ( ![C:$i]:
% 2.67/2.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.84               ( ( r1_tarski @ B @ C ) =>
% 2.67/2.84                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.67/2.84  thf('19', plain,
% 2.67/2.84      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.67/2.84         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.67/2.84          | ~ (r1_tarski @ X28 @ X30)
% 2.67/2.84          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 2.67/2.84          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.67/2.84          | ~ (l1_pre_topc @ X29))),
% 2.67/2.84      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.67/2.84  thf('20', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]:
% 2.67/2.84         (~ (l1_pre_topc @ sk_A)
% 2.67/2.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.84          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84             (k1_tops_1 @ sk_A @ X1))
% 2.67/2.84          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 2.67/2.84      inference('sup-', [status(thm)], ['18', '19'])).
% 2.67/2.84  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf('22', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]:
% 2.67/2.84         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.84          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84             (k1_tops_1 @ sk_A @ X1))
% 2.67/2.84          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 2.67/2.84      inference('demod', [status(thm)], ['20', '21'])).
% 2.67/2.84  thf('23', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 2.67/2.84          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84             (k1_tops_1 @ sk_A @ sk_B)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['13', '22'])).
% 2.67/2.84  thf(t36_xboole_1, axiom,
% 2.67/2.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.67/2.84  thf('24', plain,
% 2.67/2.84      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 2.67/2.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.67/2.84  thf('25', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84          (k1_tops_1 @ sk_A @ sk_B))),
% 2.67/2.84      inference('demod', [status(thm)], ['23', '24'])).
% 2.67/2.84  thf('26', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.67/2.84          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('demod', [status(thm)], ['16', '17'])).
% 2.67/2.84  thf(t44_tops_1, axiom,
% 2.67/2.84    (![A:$i]:
% 2.67/2.84     ( ( l1_pre_topc @ A ) =>
% 2.67/2.84       ( ![B:$i]:
% 2.67/2.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.84           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.67/2.84  thf('27', plain,
% 2.67/2.84      (![X26 : $i, X27 : $i]:
% 2.67/2.84         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.67/2.84          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 2.67/2.84          | ~ (l1_pre_topc @ X27))),
% 2.67/2.84      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.67/2.84  thf('28', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (~ (l1_pre_topc @ sk_A)
% 2.67/2.84          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84             (k4_xboole_0 @ sk_B @ X0)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['26', '27'])).
% 2.67/2.84  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf('30', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84          (k4_xboole_0 @ sk_B @ X0))),
% 2.67/2.84      inference('demod', [status(thm)], ['28', '29'])).
% 2.67/2.84  thf(t106_xboole_1, axiom,
% 2.67/2.84    (![A:$i,B:$i,C:$i]:
% 2.67/2.84     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.67/2.84       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.67/2.84  thf('31', plain,
% 2.67/2.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.67/2.84         ((r1_xboole_0 @ X3 @ X5)
% 2.67/2.84          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.84  thf('32', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 2.67/2.84      inference('sup-', [status(thm)], ['30', '31'])).
% 2.67/2.84  thf(t86_xboole_1, axiom,
% 2.67/2.84    (![A:$i,B:$i,C:$i]:
% 2.67/2.84     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.67/2.84       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.67/2.84  thf('33', plain,
% 2.67/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.67/2.84         (~ (r1_tarski @ X15 @ X16)
% 2.67/2.84          | ~ (r1_xboole_0 @ X15 @ X17)
% 2.67/2.84          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.67/2.84  thf('34', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]:
% 2.67/2.84         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84           (k4_xboole_0 @ X1 @ X0))
% 2.67/2.84          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1))),
% 2.67/2.84      inference('sup-', [status(thm)], ['32', '33'])).
% 2.67/2.84  thf('35', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.67/2.84          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 2.67/2.84      inference('sup-', [status(thm)], ['25', '34'])).
% 2.67/2.84  thf(d10_xboole_0, axiom,
% 2.67/2.84    (![A:$i,B:$i]:
% 2.67/2.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.67/2.84  thf('36', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.67/2.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.67/2.84  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.67/2.84      inference('simplify', [status(thm)], ['36'])).
% 2.67/2.84  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.67/2.84      inference('simplify', [status(thm)], ['36'])).
% 2.67/2.84  thf('39', plain,
% 2.67/2.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.67/2.84         ((r1_xboole_0 @ X3 @ X5)
% 2.67/2.84          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.84  thf('40', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.67/2.84      inference('sup-', [status(thm)], ['38', '39'])).
% 2.67/2.84  thf('41', plain,
% 2.67/2.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf('42', plain,
% 2.67/2.84      (![X26 : $i, X27 : $i]:
% 2.67/2.84         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.67/2.84          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 2.67/2.84          | ~ (l1_pre_topc @ X27))),
% 2.67/2.84      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.67/2.84  thf('43', plain,
% 2.67/2.84      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 2.67/2.84      inference('sup-', [status(thm)], ['41', '42'])).
% 2.67/2.84  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.84  thf('45', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 2.67/2.84      inference('demod', [status(thm)], ['43', '44'])).
% 2.67/2.84  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.67/2.84      inference('simplify', [status(thm)], ['36'])).
% 2.67/2.84  thf(t64_xboole_1, axiom,
% 2.67/2.84    (![A:$i,B:$i,C:$i,D:$i]:
% 2.67/2.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 2.67/2.84         ( r1_xboole_0 @ B @ D ) ) =>
% 2.67/2.84       ( r1_xboole_0 @ A @ C ) ))).
% 2.67/2.84  thf('47', plain,
% 2.67/2.84      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 2.67/2.84         ((r1_xboole_0 @ X11 @ X12)
% 2.67/2.84          | ~ (r1_tarski @ X11 @ X13)
% 2.67/2.84          | ~ (r1_tarski @ X12 @ X14)
% 2.67/2.84          | ~ (r1_xboole_0 @ X13 @ X14))),
% 2.67/2.84      inference('cnf', [status(esa)], [t64_xboole_1])).
% 2.67/2.84  thf('48', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         (~ (r1_xboole_0 @ X0 @ X1)
% 2.67/2.84          | ~ (r1_tarski @ X2 @ X1)
% 2.67/2.84          | (r1_xboole_0 @ X0 @ X2))),
% 2.67/2.84      inference('sup-', [status(thm)], ['46', '47'])).
% 2.67/2.84  thf('49', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         ((r1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 2.67/2.84          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 2.67/2.84      inference('sup-', [status(thm)], ['45', '48'])).
% 2.67/2.84  thf('50', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C))),
% 2.67/2.84      inference('sup-', [status(thm)], ['40', '49'])).
% 2.67/2.84  thf('51', plain,
% 2.67/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.67/2.84         (~ (r1_tarski @ X15 @ X16)
% 2.67/2.84          | ~ (r1_xboole_0 @ X15 @ X17)
% 2.67/2.84          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.67/2.84  thf('52', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]:
% 2.67/2.84         ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 2.67/2.84           (k4_xboole_0 @ X1 @ (k1_tops_1 @ sk_A @ sk_C)))
% 2.67/2.84          | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ X1))),
% 2.67/2.84      inference('sup-', [status(thm)], ['50', '51'])).
% 2.67/2.84  thf('53', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 2.67/2.84          (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['37', '52'])).
% 2.67/2.84  thf('54', plain,
% 2.67/2.84      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 2.67/2.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.67/2.84  thf('55', plain,
% 2.67/2.84      (![X0 : $i, X2 : $i]:
% 2.67/2.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.67/2.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.67/2.84  thf('56', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]:
% 2.67/2.84         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.67/2.84          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['54', '55'])).
% 2.67/2.84  thf('57', plain,
% 2.67/2.84      (![X0 : $i]:
% 2.67/2.84         ((k4_xboole_0 @ X0 @ sk_C)
% 2.67/2.84           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 2.67/2.84              (k1_tops_1 @ sk_A @ sk_C)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['53', '56'])).
% 2.67/2.84  thf('58', plain,
% 2.67/2.84      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 2.67/2.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.67/2.84  thf('59', plain,
% 2.67/2.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.67/2.84         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.84  thf('60', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1)),
% 2.67/2.84      inference('sup-', [status(thm)], ['58', '59'])).
% 2.67/2.84  thf('61', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.67/2.84      inference('sup-', [status(thm)], ['38', '39'])).
% 2.67/2.84  thf('62', plain,
% 2.67/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.67/2.84         (~ (r1_tarski @ X15 @ X16)
% 2.67/2.84          | ~ (r1_xboole_0 @ X15 @ X17)
% 2.67/2.84          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.67/2.84  thf('63', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 2.67/2.84          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 2.67/2.84      inference('sup-', [status(thm)], ['61', '62'])).
% 2.67/2.84  thf('64', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 2.67/2.84          (k4_xboole_0 @ X0 @ X1))),
% 2.67/2.84      inference('sup-', [status(thm)], ['60', '63'])).
% 2.67/2.84  thf('65', plain,
% 2.67/2.84      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 2.67/2.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.67/2.84  thf('66', plain,
% 2.67/2.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.67/2.84         ((r1_xboole_0 @ X3 @ X5)
% 2.67/2.84          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.84  thf('67', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 2.67/2.84      inference('sup-', [status(thm)], ['65', '66'])).
% 2.67/2.84  thf('68', plain,
% 2.67/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.67/2.84         (~ (r1_tarski @ X15 @ X16)
% 2.67/2.84          | ~ (r1_xboole_0 @ X15 @ X17)
% 2.67/2.84          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.67/2.84  thf('69', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.67/2.84         ((r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 2.67/2.84           (k4_xboole_0 @ X3 @ X0))
% 2.67/2.84          | ~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 2.67/2.84      inference('sup-', [status(thm)], ['67', '68'])).
% 2.67/2.84  thf('70', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 2.67/2.84          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 2.67/2.84      inference('sup-', [status(thm)], ['64', '69'])).
% 2.67/2.84  thf('71', plain,
% 2.67/2.84      (![X0 : $i, X2 : $i]:
% 2.67/2.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.67/2.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.67/2.84  thf('72', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         (~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 2.67/2.84             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))
% 2.67/2.84          | ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 2.67/2.84              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['70', '71'])).
% 2.67/2.84  thf('73', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 2.67/2.84          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 2.67/2.84      inference('sup-', [status(thm)], ['64', '69'])).
% 2.67/2.84  thf('74', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 2.67/2.84           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 2.67/2.84      inference('demod', [status(thm)], ['72', '73'])).
% 2.67/2.84  thf('75', plain,
% 2.67/2.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.67/2.84         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.67/2.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.84  thf('76', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.67/2.84         (~ (r1_tarski @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 2.67/2.84          | (r1_tarski @ X3 @ (k4_xboole_0 @ X2 @ X0)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['74', '75'])).
% 2.67/2.84  thf('77', plain,
% 2.67/2.84      (![X0 : $i, X1 : $i]:
% 2.67/2.84         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ sk_C))
% 2.67/2.84          | (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))))),
% 2.67/2.84      inference('sup-', [status(thm)], ['57', '76'])).
% 2.67/2.84  thf('78', plain,
% 2.67/2.84      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 2.67/2.84        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 2.67/2.84      inference('sup-', [status(thm)], ['35', '77'])).
% 2.67/2.84  thf('79', plain, ($false), inference('demod', [status(thm)], ['12', '78'])).
% 2.67/2.84  
% 2.67/2.84  % SZS output end Refutation
% 2.67/2.84  
% 2.67/2.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
