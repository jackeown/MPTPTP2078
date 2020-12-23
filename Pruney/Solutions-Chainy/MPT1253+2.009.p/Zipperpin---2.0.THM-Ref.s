%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AXwAAWegB4

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:13 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 543 expanded)
%              Number of leaves         :   34 ( 184 expanded)
%              Depth                    :   21
%              Number of atoms          :  810 (4544 expanded)
%              Number of equality atoms :   51 ( 310 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X48 @ X49 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('25',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','27'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('42',plain,(
    ! [X45: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','53','54'])).

thf('56',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','53','54'])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('63',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v4_pre_topc @ X50 @ X51 )
      | ~ ( r1_tarski @ X52 @ X50 )
      | ( r1_tarski @ ( k2_pre_topc @ X51 @ X52 ) @ X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('70',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','53','54'])).

thf('72',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['60','70','71'])).

thf('73',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('75',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AXwAAWegB4
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 1205 iterations in 0.469s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.70/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.70/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.70/0.89  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.70/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.70/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(t69_tops_1, conjecture,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_pre_topc @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89           ( ( v4_pre_topc @ B @ A ) =>
% 0.70/0.89             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i]:
% 0.70/0.89        ( ( l1_pre_topc @ A ) =>
% 0.70/0.89          ( ![B:$i]:
% 0.70/0.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89              ( ( v4_pre_topc @ B @ A ) =>
% 0.70/0.89                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.70/0.89  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(dt_k2_tops_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( l1_pre_topc @ A ) & 
% 0.70/0.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.70/0.89       ( m1_subset_1 @
% 0.70/0.89         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X48 : $i, X49 : $i]:
% 0.70/0.89         (~ (l1_pre_topc @ X48)
% 0.70/0.89          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.70/0.89          | (m1_subset_1 @ (k2_tops_1 @ X48 @ X49) @ 
% 0.70/0.89             (k1_zfmisc_1 @ (u1_struct_0 @ X48))))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.70/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.70/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('demod', [status(thm)], ['3', '4'])).
% 0.70/0.89  thf(t3_subset, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X45 : $i, X46 : $i]:
% 0.70/0.89         ((r1_tarski @ X45 @ X46) | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.70/0.89  thf(commutativity_k2_tarski, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X23 : $i, X24 : $i]:
% 0.70/0.89         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.70/0.89  thf(l51_zfmisc_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i]:
% 0.70/0.89         ((k3_tarski @ (k2_tarski @ X25 @ X26)) = (k2_xboole_0 @ X25 @ X26))),
% 0.70/0.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['8', '9'])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i]:
% 0.70/0.89         ((k3_tarski @ (k2_tarski @ X25 @ X26)) = (k2_xboole_0 @ X25 @ X26))),
% 0.70/0.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf(t3_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.89  thf('13', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.89  thf(d10_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.70/0.89      inference('simplify', [status(thm)], ['14'])).
% 0.70/0.89  thf(t43_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.70/0.89       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.70/0.89         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.70/0.89          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.70/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.70/0.89      inference('sup+', [status(thm)], ['13', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X0 : $i, X2 : $i]:
% 0.70/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.70/0.89          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.70/0.89          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['12', '20'])).
% 0.70/0.89  thf(t7_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.70/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.89  thf('23', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf('25', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['23', '24'])).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.70/0.89         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.70/0.89          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X1 @ X0)
% 0.70/0.89          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['25', '26'])).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      ((r1_tarski @ 
% 0.70/0.89        (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.70/0.89        k1_xboole_0)),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '27'])).
% 0.70/0.89  thf(t3_xboole_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (![X15 : $i]:
% 0.70/0.89         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.70/0.89         = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['28', '29'])).
% 0.70/0.89  thf(t48_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X19 : $i, X20 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.70/0.89           = (k3_xboole_0 @ X19 @ X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.70/0.89         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['30', '31'])).
% 0.70/0.89  thf('33', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.70/0.89         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('demod', [status(thm)], ['32', '33'])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (![X23 : $i, X24 : $i]:
% 0.70/0.89         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.70/0.89  thf(t12_setfam_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (![X43 : $i, X44 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.70/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['35', '36'])).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      (![X43 : $i, X44 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.70/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.70/0.89  thf('39', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['37', '38'])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.70/0.89         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['34', '39'])).
% 0.70/0.89  thf(t17_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.70/0.89      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (![X45 : $i, X47 : $i]:
% 0.70/0.89         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X45 @ X47))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.89  thf('43', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(redefinition_k4_subset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.70/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.70/0.89       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.70/0.89  thf('45', plain,
% 0.70/0.89      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.70/0.89          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 0.70/0.89          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.70/0.89            = (k2_xboole_0 @ sk_B @ X0))
% 0.70/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.70/0.89           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.70/0.89           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['43', '46'])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.70/0.89         = (k2_xboole_0 @ sk_B @ 
% 0.70/0.89            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['40', '47'])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(t65_tops_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_pre_topc @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89           ( ( k2_pre_topc @ A @ B ) =
% 0.70/0.89             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      (![X55 : $i, X56 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.70/0.89          | ((k2_pre_topc @ X56 @ X55)
% 0.70/0.89              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 0.70/0.89                 (k2_tops_1 @ X56 @ X55)))
% 0.70/0.89          | ~ (l1_pre_topc @ X56))),
% 0.70/0.89      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.89        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.70/0.89            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.70/0.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.89  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('53', plain,
% 0.70/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.70/0.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.70/0.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['51', '52'])).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.70/0.89         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['34', '39'])).
% 0.70/0.89  thf('55', plain,
% 0.70/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.70/0.89         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['48', '53', '54'])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.70/0.89         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['48', '53', '54'])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.70/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (![X0 : $i, X2 : $i]:
% 0.70/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.70/0.89          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['57', '58'])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.70/0.89        | ((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['56', '59'])).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('62', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(t31_tops_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_pre_topc @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89           ( ![C:$i]:
% 0.70/0.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.70/0.89                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.70/0.89  thf('63', plain,
% 0.70/0.89      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.70/0.89          | ~ (v4_pre_topc @ X50 @ X51)
% 0.70/0.89          | ~ (r1_tarski @ X52 @ X50)
% 0.70/0.89          | (r1_tarski @ (k2_pre_topc @ X51 @ X52) @ X50)
% 0.70/0.89          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.70/0.89          | ~ (l1_pre_topc @ X51))),
% 0.70/0.89      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.70/0.89  thf('64', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_pre_topc @ sk_A)
% 0.70/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.89          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.70/0.89          | ~ (r1_tarski @ X0 @ sk_B)
% 0.70/0.89          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['62', '63'])).
% 0.70/0.89  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('66', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('67', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.89          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.70/0.89          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.70/0.89      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.70/0.89  thf('68', plain,
% 0.70/0.89      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.70/0.89        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['61', '67'])).
% 0.70/0.89  thf('69', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.70/0.89      inference('simplify', [status(thm)], ['14'])).
% 0.70/0.89  thf('70', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 0.70/0.89      inference('demod', [status(thm)], ['68', '69'])).
% 0.70/0.89  thf('71', plain,
% 0.70/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.70/0.89         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['48', '53', '54'])).
% 0.70/0.89  thf('72', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.70/0.89      inference('demod', [status(thm)], ['60', '70', '71'])).
% 0.70/0.89  thf('73', plain,
% 0.70/0.89      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['55', '72'])).
% 0.70/0.89  thf('74', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf('75', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.70/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.89  thf('76', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['74', '75'])).
% 0.70/0.89  thf('77', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.70/0.89      inference('sup+', [status(thm)], ['73', '76'])).
% 0.70/0.89  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
