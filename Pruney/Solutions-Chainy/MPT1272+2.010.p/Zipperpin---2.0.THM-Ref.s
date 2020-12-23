%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T3R4rHmR7E

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:30 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  285 (3339 expanded)
%              Number of leaves         :   36 (1017 expanded)
%              Depth                    :   28
%              Number of atoms          : 2308 (30722 expanded)
%              Number of equality atoms :   79 ( 625 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

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

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r1_tarski @ X12 @ ( k3_subset_1 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X14 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X16 @ X15 ) @ X17 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X16 @ X17 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ sk_B @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('52',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k3_subset_1 @ sk_B @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('58',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('61',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('70',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('77',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('82',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('85',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','87'])).

thf('89',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('91',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tops_1 @ X42 @ X43 )
      | ( ( k1_tops_1 @ X43 @ X42 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('94',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) @ X34 )
      | ( v2_tops_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('100',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ X27 @ ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('105',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('111',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
       != ( k2_struct_0 @ X32 ) )
      | ( v1_tops_1 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['97','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['92','119'])).

thf('121',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['89','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['44','123'])).

thf('125',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('126',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ k1_xboole_0 )
    | ( ( k3_subset_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('129',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('133',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('135',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('140',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tops_1 @ X42 @ X43 )
      | ( ( k1_tops_1 @ X43 @ X42 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('141',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('144',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v3_tops_1 @ X35 @ X36 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X36 @ X35 ) @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['141','142','148'])).

thf('150',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['138','149'])).

thf('151',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','152'])).

thf('154',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('155',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('157',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('159',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('161',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('163',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('164',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['161','164'])).

thf('166',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','88'])).

thf('167',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['126','167'])).

thf('169',plain,(
    r1_tarski @ k1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','168'])).

thf('170',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('171',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k1_tops_1 @ X43 @ X42 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X42 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('174',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tops_1 @ X33 @ X34 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('179',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['176','183'])).

thf('185',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['171','184'])).

thf('186',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('187',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('188',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('190',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('192',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r1_tarski @ ( k1_tops_1 @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('197',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','88'])).

thf('198',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['126','167'])).

thf('199',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k1_xboole_0
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['196','199'])).

thf('201',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('202',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('203',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X18 @ X19 ) @ X19 )
      | ( X19
        = ( k2_subset_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('204',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('205',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X18 @ X19 ) @ X19 )
      | ( X19
        = ( k2_subset_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k2_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('208',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_subset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X18 @ X19 ) @ X19 )
      | ( X19 = X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['203','208'])).

thf('210',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['202','209'])).

thf('211',plain,(
    r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','152'])).

thf('212',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('213',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('214',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('216',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('218',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('219',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('221',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('223',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('225',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['162','163'])).

thf('226',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('228',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['223','228'])).

thf('230',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','229'])).

thf('231',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('233',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['223','228'])).

thf('235',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['230','235'])).

thf('237',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['210','211','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['195','237'])).

thf('239',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['190','238'])).

thf('240',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ X27 @ ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('242',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['141','142','148'])).

thf('246',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['239','244','245'])).

thf('247',plain,(
    $false ),
    inference(demod,[status(thm)],['185','246'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T3R4rHmR7E
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.38/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.62  % Solved by: fo/fo7.sh
% 1.38/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.62  % done 3242 iterations in 1.159s
% 1.38/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.62  % SZS output start Refutation
% 1.38/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.38/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.62  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 1.38/1.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.38/1.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.38/1.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.38/1.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.38/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.62  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.38/1.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.38/1.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.38/1.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.38/1.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.38/1.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.38/1.62  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.38/1.62  thf(t91_tops_1, conjecture,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( v3_tops_1 @ B @ A ) =>
% 1.38/1.62             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.38/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.62    (~( ![A:$i]:
% 1.38/1.62        ( ( l1_pre_topc @ A ) =>
% 1.38/1.62          ( ![B:$i]:
% 1.38/1.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62              ( ( v3_tops_1 @ B @ A ) =>
% 1.38/1.62                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 1.38/1.62    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 1.38/1.62  thf('0', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(t44_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.38/1.62  thf('1', plain,
% 1.38/1.62      (![X37 : $i, X38 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.38/1.62          | (r1_tarski @ (k1_tops_1 @ X38 @ X37) @ X37)
% 1.38/1.62          | ~ (l1_pre_topc @ X38))),
% 1.38/1.62      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.38/1.62  thf('2', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['0', '1'])).
% 1.38/1.62  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('4', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.38/1.62      inference('demod', [status(thm)], ['2', '3'])).
% 1.38/1.62  thf(t3_subset, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.38/1.62  thf('5', plain,
% 1.38/1.62      (![X20 : $i, X22 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('6', plain,
% 1.38/1.62      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['4', '5'])).
% 1.38/1.62  thf(dt_k3_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.38/1.62  thf('7', plain,
% 1.38/1.62      (![X7 : $i, X8 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 1.38/1.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.38/1.62  thf('8', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.38/1.62        (k1_zfmisc_1 @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['6', '7'])).
% 1.38/1.62  thf('9', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('10', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 1.38/1.62      inference('sup-', [status(thm)], ['8', '9'])).
% 1.38/1.62  thf(d10_xboole_0, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.38/1.62  thf('11', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.38/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.62  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.38/1.62      inference('simplify', [status(thm)], ['11'])).
% 1.38/1.62  thf('13', plain,
% 1.38/1.62      (![X20 : $i, X22 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('14', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf('15', plain,
% 1.38/1.62      (![X7 : $i, X8 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 1.38/1.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.38/1.62  thf('16', plain,
% 1.38/1.62      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf(t35_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( ![C:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 1.38/1.62             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.38/1.62  thf('17', plain,
% 1.38/1.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 1.38/1.62          | (r1_tarski @ X12 @ (k3_subset_1 @ X13 @ X14))
% 1.38/1.62          | ~ (r1_tarski @ X14 @ (k3_subset_1 @ X13 @ X12))
% 1.38/1.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t35_subset_1])).
% 1.38/1.62  thf('18', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.38/1.62          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)))
% 1.38/1.62          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['16', '17'])).
% 1.38/1.62  thf('19', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf(involutiveness_k3_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.38/1.62  thf('20', plain,
% 1.38/1.62      (![X9 : $i, X10 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 1.38/1.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.38/1.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.38/1.62  thf('21', plain,
% 1.38/1.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['19', '20'])).
% 1.38/1.62  thf('22', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.38/1.62          | ~ (r1_tarski @ X1 @ X0)
% 1.38/1.62          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1)))),
% 1.38/1.62      inference('demod', [status(thm)], ['18', '21'])).
% 1.38/1.62  thf('23', plain,
% 1.38/1.62      (![X20 : $i, X22 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('24', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 1.38/1.62          | ~ (r1_tarski @ X1 @ X0))),
% 1.38/1.62      inference('clc', [status(thm)], ['22', '23'])).
% 1.38/1.62  thf('25', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 1.38/1.62        (k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['10', '24'])).
% 1.38/1.62  thf('26', plain,
% 1.38/1.62      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['4', '5'])).
% 1.38/1.62  thf('27', plain,
% 1.38/1.62      (![X9 : $i, X10 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 1.38/1.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.38/1.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.38/1.62  thf('28', plain,
% 1.38/1.62      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.38/1.62         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['26', '27'])).
% 1.38/1.62  thf('29', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['25', '28'])).
% 1.38/1.62  thf('30', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('31', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('32', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.38/1.62  thf('33', plain,
% 1.38/1.62      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('34', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('35', plain, (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 1.38/1.62      inference('sup-', [status(thm)], ['33', '34'])).
% 1.38/1.62  thf(t1_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.38/1.62       ( r1_tarski @ A @ C ) ))).
% 1.38/1.62  thf('36', plain,
% 1.38/1.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.38/1.62         (~ (r1_tarski @ X3 @ X4)
% 1.38/1.62          | ~ (r1_tarski @ X4 @ X5)
% 1.38/1.62          | (r1_tarski @ X3 @ X5))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.38/1.62  thf('37', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1) | ~ (r1_tarski @ X0 @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['35', '36'])).
% 1.38/1.62  thf('38', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['32', '37'])).
% 1.38/1.62  thf('39', plain,
% 1.38/1.62      (![X20 : $i, X22 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('40', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.62  thf('41', plain,
% 1.38/1.62      (![X37 : $i, X38 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.38/1.62          | (r1_tarski @ (k1_tops_1 @ X38 @ X37) @ X37)
% 1.38/1.62          | ~ (l1_pre_topc @ X38))),
% 1.38/1.62      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.38/1.62  thf('42', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 1.38/1.62           (k3_subset_1 @ sk_B @ sk_B)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['40', '41'])).
% 1.38/1.62  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('44', plain,
% 1.38/1.62      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 1.38/1.62        (k3_subset_1 @ sk_B @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['42', '43'])).
% 1.38/1.62  thf('45', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.62  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf(t36_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( ![C:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 1.38/1.62             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 1.38/1.62  thf('47', plain,
% 1.38/1.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 1.38/1.62          | (r1_tarski @ (k3_subset_1 @ X16 @ X15) @ X17)
% 1.38/1.62          | ~ (r1_tarski @ (k3_subset_1 @ X16 @ X17) @ X15)
% 1.38/1.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t36_subset_1])).
% 1.38/1.62  thf('48', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.38/1.62          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 1.38/1.62          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['46', '47'])).
% 1.38/1.62  thf('49', plain,
% 1.38/1.62      (((r1_tarski @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 1.38/1.62         (k3_subset_1 @ sk_B @ sk_B))
% 1.38/1.62        | ~ (r1_tarski @ 
% 1.38/1.62             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 1.38/1.62             (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['45', '48'])).
% 1.38/1.62  thf('50', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.62  thf('51', plain,
% 1.38/1.62      (![X7 : $i, X8 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 1.38/1.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.38/1.62  thf('52', plain,
% 1.38/1.62      ((m1_subset_1 @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['50', '51'])).
% 1.38/1.62  thf('53', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('54', plain,
% 1.38/1.62      ((r1_tarski @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 1.38/1.62        (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['52', '53'])).
% 1.38/1.62  thf('55', plain,
% 1.38/1.62      ((r1_tarski @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 1.38/1.62        (k3_subset_1 @ sk_B @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['49', '54'])).
% 1.38/1.62  thf('56', plain,
% 1.38/1.62      (![X0 : $i, X2 : $i]:
% 1.38/1.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.62  thf('57', plain,
% 1.38/1.62      ((~ (r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 1.38/1.62           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.38/1.62        | ((k3_subset_1 @ sk_B @ sk_B)
% 1.38/1.62            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['55', '56'])).
% 1.38/1.62  thf(d3_struct_0, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.38/1.62  thf('58', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('59', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('60', plain,
% 1.38/1.62      (![X7 : $i, X8 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 1.38/1.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.38/1.62  thf('61', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['59', '60'])).
% 1.38/1.62  thf('62', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('63', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.38/1.62        (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['61', '62'])).
% 1.38/1.62  thf('64', plain,
% 1.38/1.62      (((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.38/1.62         (u1_struct_0 @ sk_A))
% 1.38/1.62        | ~ (l1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['58', '63'])).
% 1.38/1.62  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(dt_l1_pre_topc, axiom,
% 1.38/1.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.38/1.62  thf('66', plain,
% 1.38/1.62      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.38/1.62  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 1.38/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.62  thf('68', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.38/1.62        (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('demod', [status(thm)], ['64', '67'])).
% 1.38/1.62  thf('69', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 1.38/1.62          | ~ (r1_tarski @ X1 @ X0))),
% 1.38/1.62      inference('clc', [status(thm)], ['22', '23'])).
% 1.38/1.62  thf('70', plain,
% 1.38/1.62      ((r1_tarski @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['68', '69'])).
% 1.38/1.62  thf('71', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('72', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('73', plain,
% 1.38/1.62      (![X9 : $i, X10 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 1.38/1.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.38/1.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.38/1.62  thf('74', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['72', '73'])).
% 1.38/1.62  thf('75', plain,
% 1.38/1.62      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))
% 1.38/1.62        | ~ (l1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['71', '74'])).
% 1.38/1.62  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 1.38/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.62  thf('77', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['75', '76'])).
% 1.38/1.62  thf('78', plain,
% 1.38/1.62      ((r1_tarski @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)),
% 1.38/1.62      inference('demod', [status(thm)], ['70', '77'])).
% 1.38/1.62  thf('79', plain,
% 1.38/1.62      (![X20 : $i, X22 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('80', plain,
% 1.38/1.62      ((m1_subset_1 @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 1.38/1.62        (k1_zfmisc_1 @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['78', '79'])).
% 1.38/1.62  thf('81', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.38/1.62          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 1.38/1.62          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['46', '47'])).
% 1.38/1.62  thf('82', plain,
% 1.38/1.62      (((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.38/1.62        | ~ (r1_tarski @ 
% 1.38/1.62             (k3_subset_1 @ sk_B @ 
% 1.38/1.62              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 1.38/1.62             sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['80', '81'])).
% 1.38/1.62  thf('83', plain,
% 1.38/1.62      ((m1_subset_1 @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 1.38/1.62        (k1_zfmisc_1 @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['78', '79'])).
% 1.38/1.62  thf('84', plain,
% 1.38/1.62      (![X7 : $i, X8 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 1.38/1.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.38/1.62  thf('85', plain,
% 1.38/1.62      ((m1_subset_1 @ 
% 1.38/1.62        (k3_subset_1 @ sk_B @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 1.38/1.62        (k1_zfmisc_1 @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['83', '84'])).
% 1.38/1.62  thf('86', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('87', plain,
% 1.38/1.62      ((r1_tarski @ 
% 1.38/1.62        (k3_subset_1 @ sk_B @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 1.38/1.62        sk_B)),
% 1.38/1.62      inference('sup-', [status(thm)], ['85', '86'])).
% 1.38/1.62  thf('88', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['82', '87'])).
% 1.38/1.62  thf('89', plain,
% 1.38/1.62      (((k3_subset_1 @ sk_B @ sk_B)
% 1.38/1.62         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['57', '88'])).
% 1.38/1.62  thf('90', plain,
% 1.38/1.62      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf(t84_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( v2_tops_1 @ B @ A ) <=>
% 1.38/1.62             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.38/1.62  thf('91', plain,
% 1.38/1.62      (![X42 : $i, X43 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.38/1.62          | ~ (v2_tops_1 @ X42 @ X43)
% 1.38/1.62          | ((k1_tops_1 @ X43 @ X42) = (k1_xboole_0))
% 1.38/1.62          | ~ (l1_pre_topc @ X43))),
% 1.38/1.62      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.38/1.62  thf('92', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0)
% 1.38/1.62          | ((k1_tops_1 @ X0 @ 
% 1.38/1.62              (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 1.38/1.62              = (k1_xboole_0))
% 1.38/1.62          | ~ (v2_tops_1 @ 
% 1.38/1.62               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['90', '91'])).
% 1.38/1.62  thf('93', plain,
% 1.38/1.62      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf(d4_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( v2_tops_1 @ B @ A ) <=>
% 1.38/1.62             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.38/1.62  thf('94', plain,
% 1.38/1.62      (![X33 : $i, X34 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.38/1.62          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33) @ X34)
% 1.38/1.62          | (v2_tops_1 @ X33 @ X34)
% 1.38/1.62          | ~ (l1_pre_topc @ X34))),
% 1.38/1.62      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.38/1.62  thf('95', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0)
% 1.38/1.62          | (v2_tops_1 @ 
% 1.38/1.62             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 1.38/1.62          | ~ (v1_tops_1 @ 
% 1.38/1.62               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.38/1.62                (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))) @ 
% 1.38/1.62               X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['93', '94'])).
% 1.38/1.62  thf('96', plain,
% 1.38/1.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['19', '20'])).
% 1.38/1.62  thf('97', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0)
% 1.38/1.62          | (v2_tops_1 @ 
% 1.38/1.62             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 1.38/1.62          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['95', '96'])).
% 1.38/1.62  thf('98', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('99', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf(t48_pre_topc, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 1.38/1.62  thf('100', plain,
% 1.38/1.62      (![X27 : $i, X28 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.38/1.62          | (r1_tarski @ X27 @ (k2_pre_topc @ X28 @ X27))
% 1.38/1.62          | ~ (l1_pre_topc @ X28))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_pre_topc])).
% 1.38/1.62  thf('101', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0)
% 1.38/1.62          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 1.38/1.62             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['99', '100'])).
% 1.38/1.62  thf('102', plain,
% 1.38/1.62      (![X0 : $i, X2 : $i]:
% 1.38/1.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.62  thf('103', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0)
% 1.38/1.62          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 1.38/1.62               (u1_struct_0 @ X0))
% 1.38/1.62          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['101', '102'])).
% 1.38/1.62  thf('104', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf(dt_k2_pre_topc, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ( l1_pre_topc @ A ) & 
% 1.38/1.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.38/1.62       ( m1_subset_1 @
% 1.38/1.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.38/1.62  thf('105', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X24)
% 1.38/1.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.38/1.62          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 1.38/1.62             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.38/1.62  thf('106', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 1.38/1.62           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.38/1.62          | ~ (l1_pre_topc @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['104', '105'])).
% 1.38/1.62  thf('107', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('108', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0)
% 1.38/1.62          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 1.38/1.62             (u1_struct_0 @ X0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['106', '107'])).
% 1.38/1.62  thf('109', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 1.38/1.62          | ~ (l1_pre_topc @ X0))),
% 1.38/1.62      inference('clc', [status(thm)], ['103', '108'])).
% 1.38/1.62  thf('110', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf(d3_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( v1_tops_1 @ B @ A ) <=>
% 1.38/1.62             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 1.38/1.62  thf('111', plain,
% 1.38/1.62      (![X31 : $i, X32 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.38/1.62          | ((k2_pre_topc @ X32 @ X31) != (k2_struct_0 @ X32))
% 1.38/1.62          | (v1_tops_1 @ X31 @ X32)
% 1.38/1.62          | ~ (l1_pre_topc @ X32))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.38/1.62  thf('112', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0)
% 1.38/1.62          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 1.38/1.62          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['110', '111'])).
% 1.38/1.62  thf('113', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (((u1_struct_0 @ X0) != (k2_struct_0 @ X0))
% 1.38/1.62          | ~ (l1_pre_topc @ X0)
% 1.38/1.62          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 1.38/1.62          | ~ (l1_pre_topc @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['109', '112'])).
% 1.38/1.62  thf('114', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 1.38/1.62          | ~ (l1_pre_topc @ X0)
% 1.38/1.62          | ((u1_struct_0 @ X0) != (k2_struct_0 @ X0)))),
% 1.38/1.62      inference('simplify', [status(thm)], ['113'])).
% 1.38/1.62  thf('115', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 1.38/1.62          | ~ (l1_struct_0 @ X0)
% 1.38/1.62          | ~ (l1_pre_topc @ X0)
% 1.38/1.62          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['98', '114'])).
% 1.38/1.62  thf('116', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 1.38/1.62          | ~ (l1_pre_topc @ X0)
% 1.38/1.62          | ~ (l1_struct_0 @ X0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['115'])).
% 1.38/1.62  thf('117', plain,
% 1.38/1.62      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.38/1.62  thf('118', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 1.38/1.62      inference('clc', [status(thm)], ['116', '117'])).
% 1.38/1.62  thf('119', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((v2_tops_1 @ 
% 1.38/1.62           (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 1.38/1.62          | ~ (l1_pre_topc @ X0))),
% 1.38/1.62      inference('clc', [status(thm)], ['97', '118'])).
% 1.38/1.62  thf('120', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (((k1_tops_1 @ X0 @ 
% 1.38/1.62            (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 1.38/1.62            = (k1_xboole_0))
% 1.38/1.62          | ~ (l1_pre_topc @ X0))),
% 1.38/1.62      inference('clc', [status(thm)], ['92', '119'])).
% 1.38/1.62  thf('121', plain,
% 1.38/1.62      ((((k1_tops_1 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B)) = (k1_xboole_0))
% 1.38/1.62        | ~ (l1_pre_topc @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['89', '120'])).
% 1.38/1.62  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('123', plain,
% 1.38/1.62      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B)) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['121', '122'])).
% 1.38/1.62  thf('124', plain, ((r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_B @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['44', '123'])).
% 1.38/1.62  thf('125', plain,
% 1.38/1.62      (![X0 : $i, X2 : $i]:
% 1.38/1.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.62  thf('126', plain,
% 1.38/1.62      ((~ (r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ k1_xboole_0)
% 1.38/1.62        | ((k3_subset_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['124', '125'])).
% 1.38/1.62  thf('127', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('128', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X24)
% 1.38/1.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.38/1.62          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 1.38/1.62             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.38/1.62  thf('129', plain,
% 1.38/1.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.38/1.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.38/1.62        | ~ (l1_pre_topc @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['127', '128'])).
% 1.38/1.62  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('131', plain,
% 1.38/1.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['129', '130'])).
% 1.38/1.62  thf('132', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('133', plain,
% 1.38/1.62      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['131', '132'])).
% 1.38/1.62  thf('134', plain,
% 1.38/1.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['129', '130'])).
% 1.38/1.62  thf('135', plain,
% 1.38/1.62      (![X37 : $i, X38 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.38/1.62          | (r1_tarski @ (k1_tops_1 @ X38 @ X37) @ X37)
% 1.38/1.62          | ~ (l1_pre_topc @ X38))),
% 1.38/1.62      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.38/1.62  thf('136', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.38/1.62           (k2_pre_topc @ sk_A @ sk_B)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['134', '135'])).
% 1.38/1.62  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('138', plain,
% 1.38/1.62      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.38/1.62        (k2_pre_topc @ sk_A @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['136', '137'])).
% 1.38/1.62  thf('139', plain,
% 1.38/1.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['129', '130'])).
% 1.38/1.62  thf('140', plain,
% 1.38/1.62      (![X42 : $i, X43 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.38/1.62          | ~ (v2_tops_1 @ X42 @ X43)
% 1.38/1.62          | ((k1_tops_1 @ X43 @ X42) = (k1_xboole_0))
% 1.38/1.62          | ~ (l1_pre_topc @ X43))),
% 1.38/1.62      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.38/1.62  thf('141', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 1.38/1.62        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['139', '140'])).
% 1.38/1.62  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('143', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(d5_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( v3_tops_1 @ B @ A ) <=>
% 1.38/1.62             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 1.38/1.62  thf('144', plain,
% 1.38/1.62      (![X35 : $i, X36 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.38/1.62          | ~ (v3_tops_1 @ X35 @ X36)
% 1.38/1.62          | (v2_tops_1 @ (k2_pre_topc @ X36 @ X35) @ X36)
% 1.38/1.62          | ~ (l1_pre_topc @ X36))),
% 1.38/1.62      inference('cnf', [status(esa)], [d5_tops_1])).
% 1.38/1.62  thf('145', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.38/1.62        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['143', '144'])).
% 1.38/1.62  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('147', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('148', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.38/1.62      inference('demod', [status(thm)], ['145', '146', '147'])).
% 1.38/1.62  thf('149', plain,
% 1.38/1.62      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['141', '142', '148'])).
% 1.38/1.62  thf('150', plain, ((r1_tarski @ k1_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['138', '149'])).
% 1.38/1.62  thf('151', plain,
% 1.38/1.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.38/1.62         (~ (r1_tarski @ X3 @ X4)
% 1.38/1.62          | ~ (r1_tarski @ X4 @ X5)
% 1.38/1.62          | (r1_tarski @ X3 @ X5))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.38/1.62  thf('152', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.38/1.62          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['150', '151'])).
% 1.38/1.62  thf('153', plain, ((r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['133', '152'])).
% 1.38/1.62  thf('154', plain,
% 1.38/1.62      (![X20 : $i, X22 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('155', plain,
% 1.38/1.62      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['153', '154'])).
% 1.38/1.62  thf('156', plain,
% 1.38/1.62      (![X7 : $i, X8 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 1.38/1.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.38/1.62  thf('157', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['155', '156'])).
% 1.38/1.62  thf('158', plain,
% 1.38/1.62      (![X20 : $i, X21 : $i]:
% 1.38/1.62         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('159', plain,
% 1.38/1.62      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62        (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['157', '158'])).
% 1.38/1.62  thf('160', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 1.38/1.62          | ~ (r1_tarski @ X1 @ X0))),
% 1.38/1.62      inference('clc', [status(thm)], ['22', '23'])).
% 1.38/1.62  thf('161', plain,
% 1.38/1.62      ((r1_tarski @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['159', '160'])).
% 1.38/1.62  thf('162', plain,
% 1.38/1.62      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['153', '154'])).
% 1.38/1.62  thf('163', plain,
% 1.38/1.62      (![X9 : $i, X10 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 1.38/1.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.38/1.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.38/1.62  thf('164', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['162', '163'])).
% 1.38/1.62  thf('165', plain,
% 1.38/1.62      ((r1_tarski @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 1.38/1.62        k1_xboole_0)),
% 1.38/1.62      inference('demod', [status(thm)], ['161', '164'])).
% 1.38/1.62  thf('166', plain,
% 1.38/1.62      (((k3_subset_1 @ sk_B @ sk_B)
% 1.38/1.62         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['57', '88'])).
% 1.38/1.62  thf('167', plain, ((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ k1_xboole_0)),
% 1.38/1.62      inference('demod', [status(thm)], ['165', '166'])).
% 1.38/1.62  thf('168', plain, (((k3_subset_1 @ sk_B @ sk_B) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['126', '167'])).
% 1.38/1.62  thf('169', plain, ((r1_tarski @ k1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['29', '168'])).
% 1.38/1.62  thf('170', plain,
% 1.38/1.62      (![X0 : $i, X2 : $i]:
% 1.38/1.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.62  thf('171', plain,
% 1.38/1.62      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.38/1.62        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['169', '170'])).
% 1.38/1.62  thf('172', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('173', plain,
% 1.38/1.62      (![X42 : $i, X43 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.38/1.62          | ((k1_tops_1 @ X43 @ X42) != (k1_xboole_0))
% 1.38/1.62          | (v2_tops_1 @ X42 @ X43)
% 1.38/1.62          | ~ (l1_pre_topc @ X43))),
% 1.38/1.62      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.38/1.62  thf('174', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | (v2_tops_1 @ sk_B @ sk_A)
% 1.38/1.62        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['172', '173'])).
% 1.38/1.62  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('176', plain,
% 1.38/1.62      (((v2_tops_1 @ sk_B @ sk_A)
% 1.38/1.62        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['174', '175'])).
% 1.38/1.62  thf('177', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('178', plain,
% 1.38/1.62      (![X33 : $i, X34 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.38/1.62          | ~ (v2_tops_1 @ X33 @ X34)
% 1.38/1.62          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33) @ X34)
% 1.38/1.62          | ~ (l1_pre_topc @ X34))),
% 1.38/1.62      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.38/1.62  thf('179', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.38/1.62        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['177', '178'])).
% 1.38/1.62  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('181', plain,
% 1.38/1.62      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.38/1.62        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.38/1.62      inference('demod', [status(thm)], ['179', '180'])).
% 1.38/1.62  thf('182', plain,
% 1.38/1.62      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('183', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 1.38/1.62      inference('clc', [status(thm)], ['181', '182'])).
% 1.38/1.62  thf('184', plain, (((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.38/1.62      inference('clc', [status(thm)], ['176', '183'])).
% 1.38/1.62  thf('185', plain, (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 1.38/1.62      inference('simplify_reflect-', [status(thm)], ['171', '184'])).
% 1.38/1.62  thf('186', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('187', plain,
% 1.38/1.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['129', '130'])).
% 1.38/1.62  thf('188', plain,
% 1.38/1.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.38/1.62         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.38/1.62        | ~ (l1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['186', '187'])).
% 1.38/1.62  thf('189', plain, ((l1_struct_0 @ sk_A)),
% 1.38/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.62  thf('190', plain,
% 1.38/1.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['188', '189'])).
% 1.38/1.62  thf('191', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(t48_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ![C:$i]:
% 1.38/1.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62               ( ( r1_tarski @ B @ C ) =>
% 1.38/1.62                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.38/1.62  thf('192', plain,
% 1.38/1.62      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.38/1.62          | ~ (r1_tarski @ X39 @ X41)
% 1.38/1.62          | (r1_tarski @ (k1_tops_1 @ X40 @ X39) @ (k1_tops_1 @ X40 @ X41))
% 1.38/1.62          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.38/1.62          | ~ (l1_pre_topc @ X40))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.38/1.62  thf('193', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ sk_A)
% 1.38/1.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.38/1.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 1.38/1.62          | ~ (r1_tarski @ sk_B @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['191', '192'])).
% 1.38/1.62  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('195', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.38/1.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 1.38/1.62          | ~ (r1_tarski @ sk_B @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['193', '194'])).
% 1.38/1.62  thf('196', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('197', plain,
% 1.38/1.62      (((k3_subset_1 @ sk_B @ sk_B)
% 1.38/1.62         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['57', '88'])).
% 1.38/1.62  thf('198', plain, (((k3_subset_1 @ sk_B @ sk_B) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['126', '167'])).
% 1.38/1.62  thf('199', plain,
% 1.38/1.62      (((k1_xboole_0)
% 1.38/1.62         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['197', '198'])).
% 1.38/1.62  thf('200', plain,
% 1.38/1.62      ((((k1_xboole_0)
% 1.38/1.62          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.38/1.62        | ~ (l1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['196', '199'])).
% 1.38/1.62  thf('201', plain, ((l1_struct_0 @ sk_A)),
% 1.38/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.62  thf('202', plain,
% 1.38/1.62      (((k1_xboole_0)
% 1.38/1.62         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['200', '201'])).
% 1.38/1.62  thf(t39_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 1.38/1.62         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 1.38/1.62  thf('203', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         (~ (r1_tarski @ (k3_subset_1 @ X18 @ X19) @ X19)
% 1.38/1.62          | ((X19) = (k2_subset_1 @ X18))
% 1.38/1.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t39_subset_1])).
% 1.38/1.62  thf('204', plain, (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 1.38/1.62      inference('sup-', [status(thm)], ['33', '34'])).
% 1.38/1.62  thf('205', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         (~ (r1_tarski @ (k3_subset_1 @ X18 @ X19) @ X19)
% 1.38/1.62          | ((X19) = (k2_subset_1 @ X18))
% 1.38/1.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t39_subset_1])).
% 1.38/1.62  thf('206', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 1.38/1.62          | ((X0) = (k2_subset_1 @ X0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['204', '205'])).
% 1.38/1.62  thf('207', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf('208', plain, (![X0 : $i]: ((X0) = (k2_subset_1 @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['206', '207'])).
% 1.38/1.62  thf('209', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         (~ (r1_tarski @ (k3_subset_1 @ X18 @ X19) @ X19)
% 1.38/1.62          | ((X19) = (X18))
% 1.38/1.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.38/1.62      inference('demod', [status(thm)], ['203', '208'])).
% 1.38/1.62  thf('210', plain,
% 1.38/1.62      ((~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.38/1.62        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.38/1.62        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['202', '209'])).
% 1.38/1.62  thf('211', plain, ((r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['133', '152'])).
% 1.38/1.62  thf('212', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('213', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['155', '156'])).
% 1.38/1.62  thf('214', plain,
% 1.38/1.62      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.38/1.62        | ~ (l1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['212', '213'])).
% 1.38/1.62  thf('215', plain, ((l1_struct_0 @ sk_A)),
% 1.38/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.62  thf('216', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['214', '215'])).
% 1.38/1.62  thf('217', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('218', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['155', '156'])).
% 1.38/1.62  thf('219', plain,
% 1.38/1.62      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.38/1.62        | ~ (l1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['217', '218'])).
% 1.38/1.62  thf('220', plain, ((l1_struct_0 @ sk_A)),
% 1.38/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.62  thf('221', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['219', '220'])).
% 1.38/1.62  thf('222', plain,
% 1.38/1.62      (![X9 : $i, X10 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 1.38/1.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.38/1.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.38/1.62  thf('223', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)))
% 1.38/1.62         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['221', '222'])).
% 1.38/1.62  thf('224', plain,
% 1.38/1.62      (![X23 : $i]:
% 1.38/1.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.38/1.62  thf('225', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['162', '163'])).
% 1.38/1.62  thf('226', plain,
% 1.38/1.62      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))
% 1.38/1.62        | ~ (l1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['224', '225'])).
% 1.38/1.62  thf('227', plain, ((l1_struct_0 @ sk_A)),
% 1.38/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.62  thf('228', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['226', '227'])).
% 1.38/1.62  thf('229', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.38/1.62         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['223', '228'])).
% 1.38/1.62  thf('230', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['216', '229'])).
% 1.38/1.62  thf('231', plain,
% 1.38/1.62      (((k1_xboole_0)
% 1.38/1.62         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['197', '198'])).
% 1.38/1.62  thf('232', plain,
% 1.38/1.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['19', '20'])).
% 1.38/1.62  thf('233', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.38/1.62         = (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup+', [status(thm)], ['231', '232'])).
% 1.38/1.62  thf('234', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.38/1.62         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['223', '228'])).
% 1.38/1.62  thf('235', plain,
% 1.38/1.62      (((u1_struct_0 @ sk_A)
% 1.38/1.62         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['233', '234'])).
% 1.38/1.62  thf('236', plain,
% 1.38/1.62      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['230', '235'])).
% 1.38/1.62  thf('237', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.38/1.62      inference('demod', [status(thm)], ['210', '211', '236'])).
% 1.38/1.62  thf('238', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.38/1.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 1.38/1.62          | ~ (r1_tarski @ sk_B @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['195', '237'])).
% 1.38/1.62  thf('239', plain,
% 1.38/1.62      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 1.38/1.62        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.38/1.62           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['190', '238'])).
% 1.38/1.62  thf('240', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('241', plain,
% 1.38/1.62      (![X27 : $i, X28 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.38/1.62          | (r1_tarski @ X27 @ (k2_pre_topc @ X28 @ X27))
% 1.38/1.62          | ~ (l1_pre_topc @ X28))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_pre_topc])).
% 1.38/1.62  thf('242', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['240', '241'])).
% 1.38/1.62  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('244', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['242', '243'])).
% 1.38/1.62  thf('245', plain,
% 1.38/1.62      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['141', '142', '148'])).
% 1.38/1.62  thf('246', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 1.38/1.62      inference('demod', [status(thm)], ['239', '244', '245'])).
% 1.38/1.62  thf('247', plain, ($false), inference('demod', [status(thm)], ['185', '246'])).
% 1.38/1.62  
% 1.38/1.62  % SZS output end Refutation
% 1.38/1.62  
% 1.47/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
