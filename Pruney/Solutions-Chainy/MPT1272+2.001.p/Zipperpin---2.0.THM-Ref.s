%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ApmnJCDJMt

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:28 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 551 expanded)
%              Number of leaves         :   42 ( 185 expanded)
%              Depth                    :   17
%              Number of atoms          : 1081 (4809 expanded)
%              Number of equality atoms :   46 ( 239 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

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
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( r1_tarski @ X63 @ ( k2_tops_1 @ X64 @ X63 ) )
      | ( v2_tops_1 @ X63 @ X64 )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v2_tops_1 @ X51 @ X52 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X52 ) @ X51 ) @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,(
    ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['4','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X55 @ X56 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','42'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X30 @ X29 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','53'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('56',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('59',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k2_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('64',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_pre_topc @ X60 @ X59 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','53'])).

thf('69',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','67','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('71',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','67','68'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('76',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('78',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X62 @ ( k2_pre_topc @ X62 @ X61 ) ) @ ( k2_tops_1 @ X62 @ X61 ) )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('83',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X49 @ X50 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( v2_tops_1 @ X63 @ X64 )
      | ( r1_tarski @ X63 @ ( k2_tops_1 @ X64 @ X63 ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('91',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v3_tops_1 @ X53 @ X54 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X54 @ X53 ) @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','95'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('97',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','98'])).

thf('100',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','67','68'])).

thf('101',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['76','99','100'])).

thf('102',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['17','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ApmnJCDJMt
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:36:06 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.06/3.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.06/3.28  % Solved by: fo/fo7.sh
% 3.06/3.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.06/3.28  % done 7793 iterations in 2.826s
% 3.06/3.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.06/3.28  % SZS output start Refutation
% 3.06/3.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.06/3.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.06/3.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.06/3.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.06/3.28  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 3.06/3.28  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 3.06/3.28  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.06/3.28  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 3.06/3.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.06/3.28  thf(sk_B_type, type, sk_B: $i).
% 3.06/3.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.06/3.28  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.06/3.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.06/3.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.06/3.28  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.06/3.28  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.06/3.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.06/3.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.06/3.28  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.06/3.28  thf(sk_A_type, type, sk_A: $i).
% 3.06/3.28  thf(t91_tops_1, conjecture,
% 3.06/3.28    (![A:$i]:
% 3.06/3.28     ( ( l1_pre_topc @ A ) =>
% 3.06/3.28       ( ![B:$i]:
% 3.06/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.06/3.28           ( ( v3_tops_1 @ B @ A ) =>
% 3.06/3.28             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 3.06/3.28  thf(zf_stmt_0, negated_conjecture,
% 3.06/3.28    (~( ![A:$i]:
% 3.06/3.28        ( ( l1_pre_topc @ A ) =>
% 3.06/3.28          ( ![B:$i]:
% 3.06/3.28            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.06/3.28              ( ( v3_tops_1 @ B @ A ) =>
% 3.06/3.28                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 3.06/3.28    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 3.06/3.28  thf('0', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(t88_tops_1, axiom,
% 3.06/3.28    (![A:$i]:
% 3.06/3.28     ( ( l1_pre_topc @ A ) =>
% 3.06/3.28       ( ![B:$i]:
% 3.06/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.06/3.28           ( ( v2_tops_1 @ B @ A ) <=>
% 3.06/3.28             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.06/3.28  thf('1', plain,
% 3.06/3.28      (![X63 : $i, X64 : $i]:
% 3.06/3.28         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 3.06/3.28          | ~ (r1_tarski @ X63 @ (k2_tops_1 @ X64 @ X63))
% 3.06/3.28          | (v2_tops_1 @ X63 @ X64)
% 3.06/3.28          | ~ (l1_pre_topc @ X64))),
% 3.06/3.28      inference('cnf', [status(esa)], [t88_tops_1])).
% 3.06/3.28  thf('2', plain,
% 3.06/3.28      ((~ (l1_pre_topc @ sk_A)
% 3.06/3.28        | (v2_tops_1 @ sk_B @ sk_A)
% 3.06/3.28        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('sup-', [status(thm)], ['0', '1'])).
% 3.06/3.28  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('4', plain,
% 3.06/3.28      (((v2_tops_1 @ sk_B @ sk_A)
% 3.06/3.28        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['2', '3'])).
% 3.06/3.28  thf('5', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(d4_tops_1, axiom,
% 3.06/3.28    (![A:$i]:
% 3.06/3.28     ( ( l1_pre_topc @ A ) =>
% 3.06/3.28       ( ![B:$i]:
% 3.06/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.06/3.28           ( ( v2_tops_1 @ B @ A ) <=>
% 3.06/3.28             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 3.06/3.28  thf('6', plain,
% 3.06/3.28      (![X51 : $i, X52 : $i]:
% 3.06/3.28         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 3.06/3.28          | ~ (v2_tops_1 @ X51 @ X52)
% 3.06/3.28          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X52) @ X51) @ X52)
% 3.06/3.28          | ~ (l1_pre_topc @ X52))),
% 3.06/3.28      inference('cnf', [status(esa)], [d4_tops_1])).
% 3.06/3.28  thf('7', plain,
% 3.06/3.28      ((~ (l1_pre_topc @ sk_A)
% 3.06/3.28        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.06/3.28        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 3.06/3.28      inference('sup-', [status(thm)], ['5', '6'])).
% 3.06/3.28  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('9', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(d5_subset_1, axiom,
% 3.06/3.28    (![A:$i,B:$i]:
% 3.06/3.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.06/3.28       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.06/3.28  thf('10', plain,
% 3.06/3.28      (![X31 : $i, X32 : $i]:
% 3.06/3.28         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 3.06/3.28          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 3.06/3.28      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.06/3.28  thf('11', plain,
% 3.06/3.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.06/3.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.06/3.28      inference('sup-', [status(thm)], ['9', '10'])).
% 3.06/3.28  thf('12', plain,
% 3.06/3.28      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.06/3.28        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 3.06/3.28      inference('demod', [status(thm)], ['7', '8', '11'])).
% 3.06/3.28  thf('13', plain,
% 3.06/3.28      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('14', plain,
% 3.06/3.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.06/3.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.06/3.28      inference('sup-', [status(thm)], ['9', '10'])).
% 3.06/3.28  thf('15', plain,
% 3.06/3.28      (~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 3.06/3.28      inference('demod', [status(thm)], ['13', '14'])).
% 3.06/3.28  thf('16', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 3.06/3.28      inference('clc', [status(thm)], ['12', '15'])).
% 3.06/3.28  thf('17', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 3.06/3.28      inference('clc', [status(thm)], ['4', '16'])).
% 3.06/3.28  thf('18', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(dt_k2_tops_1, axiom,
% 3.06/3.28    (![A:$i,B:$i]:
% 3.06/3.28     ( ( ( l1_pre_topc @ A ) & 
% 3.06/3.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.06/3.28       ( m1_subset_1 @
% 3.06/3.28         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.06/3.28  thf('19', plain,
% 3.06/3.28      (![X55 : $i, X56 : $i]:
% 3.06/3.28         (~ (l1_pre_topc @ X55)
% 3.06/3.28          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 3.06/3.28          | (m1_subset_1 @ (k2_tops_1 @ X55 @ X56) @ 
% 3.06/3.28             (k1_zfmisc_1 @ (u1_struct_0 @ X55))))),
% 3.06/3.28      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.06/3.28  thf('20', plain,
% 3.06/3.28      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.06/3.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.06/3.28        | ~ (l1_pre_topc @ sk_A))),
% 3.06/3.28      inference('sup-', [status(thm)], ['18', '19'])).
% 3.06/3.28  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('22', plain,
% 3.06/3.28      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.06/3.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('demod', [status(thm)], ['20', '21'])).
% 3.06/3.28  thf(t3_subset, axiom,
% 3.06/3.28    (![A:$i,B:$i]:
% 3.06/3.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.06/3.28  thf('23', plain,
% 3.06/3.28      (![X46 : $i, X47 : $i]:
% 3.06/3.28         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 3.06/3.28      inference('cnf', [status(esa)], [t3_subset])).
% 3.06/3.28  thf('24', plain,
% 3.06/3.28      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 3.06/3.28      inference('sup-', [status(thm)], ['22', '23'])).
% 3.06/3.28  thf(t3_boole, axiom,
% 3.06/3.28    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.06/3.28  thf('25', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 3.06/3.28      inference('cnf', [status(esa)], [t3_boole])).
% 3.06/3.28  thf(d10_xboole_0, axiom,
% 3.06/3.28    (![A:$i,B:$i]:
% 3.06/3.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.06/3.28  thf('26', plain,
% 3.06/3.28      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 3.06/3.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.06/3.28  thf('27', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 3.06/3.28      inference('simplify', [status(thm)], ['26'])).
% 3.06/3.28  thf(t43_xboole_1, axiom,
% 3.06/3.28    (![A:$i,B:$i,C:$i]:
% 3.06/3.28     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.06/3.28       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.06/3.28  thf('28', plain,
% 3.06/3.28      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.06/3.28         ((r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 3.06/3.28          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 3.06/3.28      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.06/3.28  thf('29', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]:
% 3.06/3.28         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 3.06/3.28      inference('sup-', [status(thm)], ['27', '28'])).
% 3.06/3.28  thf('30', plain,
% 3.06/3.28      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 3.06/3.28      inference('sup+', [status(thm)], ['25', '29'])).
% 3.06/3.28  thf('31', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 3.06/3.28      inference('simplify', [status(thm)], ['26'])).
% 3.06/3.28  thf(commutativity_k2_xboole_0, axiom,
% 3.06/3.28    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.06/3.28  thf('32', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.06/3.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.06/3.28  thf(t11_xboole_1, axiom,
% 3.06/3.28    (![A:$i,B:$i,C:$i]:
% 3.06/3.28     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 3.06/3.28  thf('33', plain,
% 3.06/3.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.06/3.28         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 3.06/3.28      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.06/3.28  thf('34', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.06/3.28         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 3.06/3.28      inference('sup-', [status(thm)], ['32', '33'])).
% 3.06/3.28  thf('35', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.06/3.28      inference('sup-', [status(thm)], ['31', '34'])).
% 3.06/3.28  thf('36', plain,
% 3.06/3.28      (![X2 : $i, X4 : $i]:
% 3.06/3.28         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.06/3.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.06/3.28  thf('37', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]:
% 3.06/3.28         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 3.06/3.28          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 3.06/3.28      inference('sup-', [status(thm)], ['35', '36'])).
% 3.06/3.28  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.06/3.28      inference('sup-', [status(thm)], ['30', '37'])).
% 3.06/3.28  thf('39', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.06/3.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.06/3.28  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.06/3.28      inference('sup+', [status(thm)], ['38', '39'])).
% 3.06/3.28  thf('41', plain,
% 3.06/3.28      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.06/3.28         ((r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 3.06/3.28          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 3.06/3.28      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.06/3.28  thf('42', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]:
% 3.06/3.28         (~ (r1_tarski @ X1 @ X0)
% 3.06/3.28          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 3.06/3.28      inference('sup-', [status(thm)], ['40', '41'])).
% 3.06/3.28  thf('43', plain,
% 3.06/3.28      ((r1_tarski @ 
% 3.06/3.28        (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.06/3.28        k1_xboole_0)),
% 3.06/3.28      inference('sup-', [status(thm)], ['24', '42'])).
% 3.06/3.28  thf(t3_xboole_1, axiom,
% 3.06/3.28    (![A:$i]:
% 3.06/3.28     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.06/3.28  thf('44', plain,
% 3.06/3.28      (![X20 : $i]:
% 3.06/3.28         (((X20) = (k1_xboole_0)) | ~ (r1_tarski @ X20 @ k1_xboole_0))),
% 3.06/3.28      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.06/3.28  thf('45', plain,
% 3.06/3.28      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.06/3.28         = (k1_xboole_0))),
% 3.06/3.28      inference('sup-', [status(thm)], ['43', '44'])).
% 3.06/3.28  thf(t48_xboole_1, axiom,
% 3.06/3.28    (![A:$i,B:$i]:
% 3.06/3.28     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.06/3.28  thf('46', plain,
% 3.06/3.28      (![X27 : $i, X28 : $i]:
% 3.06/3.28         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 3.06/3.28           = (k3_xboole_0 @ X27 @ X28))),
% 3.06/3.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.06/3.28  thf('47', plain,
% 3.06/3.28      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 3.06/3.28         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('sup+', [status(thm)], ['45', '46'])).
% 3.06/3.28  thf('48', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 3.06/3.28      inference('cnf', [status(esa)], [t3_boole])).
% 3.06/3.28  thf(commutativity_k2_tarski, axiom,
% 3.06/3.28    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.06/3.28  thf('49', plain,
% 3.06/3.28      (![X29 : $i, X30 : $i]:
% 3.06/3.28         ((k2_tarski @ X30 @ X29) = (k2_tarski @ X29 @ X30))),
% 3.06/3.28      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.06/3.28  thf(t12_setfam_1, axiom,
% 3.06/3.28    (![A:$i,B:$i]:
% 3.06/3.28     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.06/3.28  thf('50', plain,
% 3.06/3.28      (![X44 : $i, X45 : $i]:
% 3.06/3.28         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 3.06/3.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.06/3.28  thf('51', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]:
% 3.06/3.28         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.06/3.28      inference('sup+', [status(thm)], ['49', '50'])).
% 3.06/3.28  thf('52', plain,
% 3.06/3.28      (![X44 : $i, X45 : $i]:
% 3.06/3.28         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 3.06/3.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.06/3.28  thf('53', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.06/3.28      inference('sup+', [status(thm)], ['51', '52'])).
% 3.06/3.28  thf('54', plain,
% 3.06/3.28      (((k2_tops_1 @ sk_A @ sk_B)
% 3.06/3.28         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['47', '48', '53'])).
% 3.06/3.28  thf(t17_xboole_1, axiom,
% 3.06/3.28    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.06/3.28  thf('55', plain,
% 3.06/3.28      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 3.06/3.28      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.06/3.28  thf('56', plain,
% 3.06/3.28      (![X46 : $i, X48 : $i]:
% 3.06/3.28         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 3.06/3.28      inference('cnf', [status(esa)], [t3_subset])).
% 3.06/3.28  thf('57', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]:
% 3.06/3.28         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.06/3.28      inference('sup-', [status(thm)], ['55', '56'])).
% 3.06/3.28  thf('58', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(redefinition_k4_subset_1, axiom,
% 3.06/3.28    (![A:$i,B:$i,C:$i]:
% 3.06/3.28     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.06/3.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.06/3.28       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.06/3.28  thf('59', plain,
% 3.06/3.28      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.06/3.28         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 3.06/3.28          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 3.06/3.28          | ((k4_subset_1 @ X36 @ X35 @ X37) = (k2_xboole_0 @ X35 @ X37)))),
% 3.06/3.28      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.06/3.28  thf('60', plain,
% 3.06/3.28      (![X0 : $i]:
% 3.06/3.28         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.06/3.28            = (k2_xboole_0 @ sk_B @ X0))
% 3.06/3.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.06/3.28      inference('sup-', [status(thm)], ['58', '59'])).
% 3.06/3.28  thf('61', plain,
% 3.06/3.28      (![X0 : $i]:
% 3.06/3.28         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.06/3.28           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 3.06/3.28           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 3.06/3.28      inference('sup-', [status(thm)], ['57', '60'])).
% 3.06/3.28  thf('62', plain,
% 3.06/3.28      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.06/3.28         = (k2_xboole_0 @ sk_B @ 
% 3.06/3.28            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 3.06/3.28      inference('sup+', [status(thm)], ['54', '61'])).
% 3.06/3.28  thf('63', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(t65_tops_1, axiom,
% 3.06/3.28    (![A:$i]:
% 3.06/3.28     ( ( l1_pre_topc @ A ) =>
% 3.06/3.28       ( ![B:$i]:
% 3.06/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.06/3.28           ( ( k2_pre_topc @ A @ B ) =
% 3.06/3.28             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.06/3.28  thf('64', plain,
% 3.06/3.28      (![X59 : $i, X60 : $i]:
% 3.06/3.28         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 3.06/3.28          | ((k2_pre_topc @ X60 @ X59)
% 3.06/3.28              = (k4_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 3.06/3.28                 (k2_tops_1 @ X60 @ X59)))
% 3.06/3.28          | ~ (l1_pre_topc @ X60))),
% 3.06/3.28      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.06/3.28  thf('65', plain,
% 3.06/3.28      ((~ (l1_pre_topc @ sk_A)
% 3.06/3.28        | ((k2_pre_topc @ sk_A @ sk_B)
% 3.06/3.28            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.06/3.28               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.06/3.28      inference('sup-', [status(thm)], ['63', '64'])).
% 3.06/3.28  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('67', plain,
% 3.06/3.28      (((k2_pre_topc @ sk_A @ sk_B)
% 3.06/3.28         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.06/3.28            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['65', '66'])).
% 3.06/3.28  thf('68', plain,
% 3.06/3.28      (((k2_tops_1 @ sk_A @ sk_B)
% 3.06/3.28         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['47', '48', '53'])).
% 3.06/3.28  thf('69', plain,
% 3.06/3.28      (((k2_pre_topc @ sk_A @ sk_B)
% 3.06/3.28         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['62', '67', '68'])).
% 3.06/3.28  thf('70', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 3.06/3.28      inference('simplify', [status(thm)], ['26'])).
% 3.06/3.28  thf('71', plain,
% 3.06/3.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.06/3.28         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 3.06/3.28      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.06/3.28  thf('72', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.06/3.28      inference('sup-', [status(thm)], ['70', '71'])).
% 3.06/3.28  thf('73', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 3.06/3.28      inference('sup+', [status(thm)], ['69', '72'])).
% 3.06/3.28  thf('74', plain,
% 3.06/3.28      (((k2_pre_topc @ sk_A @ sk_B)
% 3.06/3.28         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['62', '67', '68'])).
% 3.06/3.28  thf('75', plain,
% 3.06/3.28      (![X0 : $i, X1 : $i]:
% 3.06/3.28         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 3.06/3.28          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 3.06/3.28      inference('sup-', [status(thm)], ['35', '36'])).
% 3.06/3.28  thf('76', plain,
% 3.06/3.28      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 3.06/3.28        | ((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.06/3.28            = (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('sup-', [status(thm)], ['74', '75'])).
% 3.06/3.28  thf('77', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(t72_tops_1, axiom,
% 3.06/3.28    (![A:$i]:
% 3.06/3.28     ( ( l1_pre_topc @ A ) =>
% 3.06/3.28       ( ![B:$i]:
% 3.06/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.06/3.28           ( r1_tarski @
% 3.06/3.28             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 3.06/3.28             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 3.06/3.28  thf('78', plain,
% 3.06/3.28      (![X61 : $i, X62 : $i]:
% 3.06/3.28         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 3.06/3.28          | (r1_tarski @ (k2_tops_1 @ X62 @ (k2_pre_topc @ X62 @ X61)) @ 
% 3.06/3.28             (k2_tops_1 @ X62 @ X61))
% 3.06/3.28          | ~ (l1_pre_topc @ X62))),
% 3.06/3.28      inference('cnf', [status(esa)], [t72_tops_1])).
% 3.06/3.28  thf('79', plain,
% 3.06/3.28      ((~ (l1_pre_topc @ sk_A)
% 3.06/3.28        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.06/3.28           (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('sup-', [status(thm)], ['77', '78'])).
% 3.06/3.28  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('81', plain,
% 3.06/3.28      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.06/3.28        (k2_tops_1 @ sk_A @ sk_B))),
% 3.06/3.28      inference('demod', [status(thm)], ['79', '80'])).
% 3.06/3.28  thf('82', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(dt_k2_pre_topc, axiom,
% 3.06/3.28    (![A:$i,B:$i]:
% 3.06/3.28     ( ( ( l1_pre_topc @ A ) & 
% 3.06/3.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.06/3.28       ( m1_subset_1 @
% 3.06/3.28         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.06/3.28  thf('83', plain,
% 3.06/3.28      (![X49 : $i, X50 : $i]:
% 3.06/3.28         (~ (l1_pre_topc @ X49)
% 3.06/3.28          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 3.06/3.28          | (m1_subset_1 @ (k2_pre_topc @ X49 @ X50) @ 
% 3.06/3.28             (k1_zfmisc_1 @ (u1_struct_0 @ X49))))),
% 3.06/3.28      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.06/3.28  thf('84', plain,
% 3.06/3.28      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.06/3.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.06/3.28        | ~ (l1_pre_topc @ sk_A))),
% 3.06/3.28      inference('sup-', [status(thm)], ['82', '83'])).
% 3.06/3.28  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('86', plain,
% 3.06/3.28      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.06/3.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('demod', [status(thm)], ['84', '85'])).
% 3.06/3.28  thf('87', plain,
% 3.06/3.28      (![X63 : $i, X64 : $i]:
% 3.06/3.28         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 3.06/3.28          | ~ (v2_tops_1 @ X63 @ X64)
% 3.06/3.28          | (r1_tarski @ X63 @ (k2_tops_1 @ X64 @ X63))
% 3.06/3.28          | ~ (l1_pre_topc @ X64))),
% 3.06/3.28      inference('cnf', [status(esa)], [t88_tops_1])).
% 3.06/3.28  thf('88', plain,
% 3.06/3.28      ((~ (l1_pre_topc @ sk_A)
% 3.06/3.28        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.06/3.28           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.06/3.28        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 3.06/3.28      inference('sup-', [status(thm)], ['86', '87'])).
% 3.06/3.28  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('90', plain,
% 3.06/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf(d5_tops_1, axiom,
% 3.06/3.28    (![A:$i]:
% 3.06/3.28     ( ( l1_pre_topc @ A ) =>
% 3.06/3.28       ( ![B:$i]:
% 3.06/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.06/3.28           ( ( v3_tops_1 @ B @ A ) <=>
% 3.06/3.28             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 3.06/3.28  thf('91', plain,
% 3.06/3.28      (![X53 : $i, X54 : $i]:
% 3.06/3.28         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 3.06/3.28          | ~ (v3_tops_1 @ X53 @ X54)
% 3.06/3.28          | (v2_tops_1 @ (k2_pre_topc @ X54 @ X53) @ X54)
% 3.06/3.28          | ~ (l1_pre_topc @ X54))),
% 3.06/3.28      inference('cnf', [status(esa)], [d5_tops_1])).
% 3.06/3.28  thf('92', plain,
% 3.06/3.28      ((~ (l1_pre_topc @ sk_A)
% 3.06/3.28        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.06/3.28        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 3.06/3.28      inference('sup-', [status(thm)], ['90', '91'])).
% 3.06/3.28  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('94', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 3.06/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.28  thf('95', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.06/3.28      inference('demod', [status(thm)], ['92', '93', '94'])).
% 3.06/3.28  thf('96', plain,
% 3.06/3.28      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.06/3.28        (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['88', '89', '95'])).
% 3.06/3.28  thf(t1_xboole_1, axiom,
% 3.06/3.28    (![A:$i,B:$i,C:$i]:
% 3.06/3.28     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.06/3.28       ( r1_tarski @ A @ C ) ))).
% 3.06/3.28  thf('97', plain,
% 3.06/3.28      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.06/3.28         (~ (r1_tarski @ X12 @ X13)
% 3.06/3.28          | ~ (r1_tarski @ X13 @ X14)
% 3.06/3.28          | (r1_tarski @ X12 @ X14))),
% 3.06/3.28      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.06/3.28  thf('98', plain,
% 3.06/3.28      (![X0 : $i]:
% 3.06/3.28         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 3.06/3.28          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.06/3.28               X0))),
% 3.06/3.28      inference('sup-', [status(thm)], ['96', '97'])).
% 3.06/3.28  thf('99', plain,
% 3.06/3.28      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 3.06/3.28      inference('sup-', [status(thm)], ['81', '98'])).
% 3.06/3.28  thf('100', plain,
% 3.06/3.28      (((k2_pre_topc @ sk_A @ sk_B)
% 3.06/3.28         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.06/3.28      inference('demod', [status(thm)], ['62', '67', '68'])).
% 3.06/3.28  thf('101', plain,
% 3.06/3.28      (((k2_pre_topc @ sk_A @ sk_B) = (k2_tops_1 @ sk_A @ sk_B))),
% 3.06/3.28      inference('demod', [status(thm)], ['76', '99', '100'])).
% 3.06/3.28  thf('102', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 3.06/3.28      inference('demod', [status(thm)], ['73', '101'])).
% 3.06/3.28  thf('103', plain, ($false), inference('demod', [status(thm)], ['17', '102'])).
% 3.06/3.28  
% 3.06/3.28  % SZS output end Refutation
% 3.06/3.28  
% 3.06/3.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
