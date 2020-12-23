%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bO63hmPKLR

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:30 EST 2020

% Result     : Theorem 7.24s
% Output     : Refutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  256 (2948 expanded)
%              Number of leaves         :   33 ( 902 expanded)
%              Depth                    :   28
%              Number of atoms          : 2274 (25586 expanded)
%              Number of equality atoms :   78 ( 757 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v1_tops_1 @ X31 @ X32 )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k2_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X24 @ ( k2_pre_topc @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
       != ( k2_struct_0 @ X32 ) )
      | ( v1_tops_1 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['18','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('60',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['45','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('72',plain,(
    r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( r1_tarski @ X11 @ ( k3_subset_1 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('77',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','81'])).

thf('83',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('89',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('94',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X15 @ X14 ) @ X16 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X15 @ X16 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('99',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ sk_B @ sk_B ) )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('107',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('109',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('110',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) )
    = ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['104','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('114',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','114'])).

thf('116',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','120'])).

thf('122',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('123',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('125',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('128',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
       != ( k2_struct_0 @ X32 ) )
      | ( v1_tops_1 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('136',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['125','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('139',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('140',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('144',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('145',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('148',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('152',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('154',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k1_tops_1 @ X30 @ X29 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k2_pre_topc @ X30 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('155',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('158',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','158'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('160',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( r1_tarski @ X26 @ X28 )
      | ( r1_tarski @ ( k2_pre_topc @ X27 @ X26 ) @ ( k2_pre_topc @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('165',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('166',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('167',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('168',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('170',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('172',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('174',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('175',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k1_tops_1 @ X30 @ X29 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k2_pre_topc @ X30 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('176',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['87','88'])).

thf('179',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['173','179'])).

thf('181',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('182',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','182'])).

thf('184',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('185',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v1_tops_1 @ X31 @ X32 )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k2_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_tops_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','188'])).

thf('190',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['18','40'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('195',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tops_1 @ X33 @ X34 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v2_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tops_1 @ X1 @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['190','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('201',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v3_tops_1 @ X35 @ X36 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X36 @ X35 ) @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('202',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['198','199','205'])).

thf('207',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('208',plain,(
    v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','208'])).

thf('210',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['163','164','165','209','210'])).

thf('212',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','211'])).

thf('213',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('214',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('217',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('219',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['212','219'])).

thf('221',plain,(
    $false ),
    inference(demod,[status(thm)],['137','220'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bO63hmPKLR
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.24/7.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.24/7.43  % Solved by: fo/fo7.sh
% 7.24/7.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.24/7.43  % done 15089 iterations in 6.969s
% 7.24/7.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.24/7.43  % SZS output start Refutation
% 7.24/7.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.24/7.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.24/7.43  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 7.24/7.43  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 7.24/7.43  thf(sk_A_type, type, sk_A: $i).
% 7.24/7.43  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 7.24/7.43  thf(sk_B_type, type, sk_B: $i).
% 7.24/7.43  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 7.24/7.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.24/7.43  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 7.24/7.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.24/7.43  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.24/7.43  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 7.24/7.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.24/7.43  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.24/7.43  thf(d3_struct_0, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 7.24/7.43  thf('0', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf(t91_tops_1, conjecture,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( ( v3_tops_1 @ B @ A ) =>
% 7.24/7.43             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 7.24/7.43  thf(zf_stmt_0, negated_conjecture,
% 7.24/7.43    (~( ![A:$i]:
% 7.24/7.43        ( ( l1_pre_topc @ A ) =>
% 7.24/7.43          ( ![B:$i]:
% 7.24/7.43            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43              ( ( v3_tops_1 @ B @ A ) =>
% 7.24/7.43                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 7.24/7.43    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 7.24/7.43  thf('1', plain,
% 7.24/7.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf(dt_k3_subset_1, axiom,
% 7.24/7.43    (![A:$i,B:$i]:
% 7.24/7.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.43       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.24/7.43  thf('2', plain,
% 7.24/7.43      (![X7 : $i, X8 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 7.24/7.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.24/7.43  thf('3', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['1', '2'])).
% 7.24/7.43  thf('4', plain,
% 7.24/7.43      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['0', '3'])).
% 7.24/7.43  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf(dt_l1_pre_topc, axiom,
% 7.24/7.43    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 7.24/7.43  thf('6', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 7.24/7.43  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('8', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['4', '7'])).
% 7.24/7.43  thf(dt_k2_pre_topc, axiom,
% 7.24/7.43    (![A:$i,B:$i]:
% 7.24/7.43     ( ( ( l1_pre_topc @ A ) & 
% 7.24/7.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.24/7.43       ( m1_subset_1 @
% 7.24/7.43         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.24/7.43  thf('9', plain,
% 7.24/7.43      (![X21 : $i, X22 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X21)
% 7.24/7.43          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 7.24/7.43          | (m1_subset_1 @ (k2_pre_topc @ X21 @ X22) @ 
% 7.24/7.43             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.24/7.43  thf('10', plain,
% 7.24/7.43      (((m1_subset_1 @ 
% 7.24/7.43         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.24/7.43        | ~ (l1_pre_topc @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['8', '9'])).
% 7.24/7.43  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('12', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['10', '11'])).
% 7.24/7.43  thf(d10_xboole_0, axiom,
% 7.24/7.43    (![A:$i,B:$i]:
% 7.24/7.43     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.24/7.43  thf('13', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 7.24/7.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.24/7.43  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 7.24/7.43      inference('simplify', [status(thm)], ['13'])).
% 7.24/7.43  thf(t3_subset, axiom,
% 7.24/7.43    (![A:$i,B:$i]:
% 7.24/7.43     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.24/7.43  thf('15', plain,
% 7.24/7.43      (![X17 : $i, X19 : $i]:
% 7.24/7.43         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('16', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['14', '15'])).
% 7.24/7.43  thf(d3_tops_1, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( ( v1_tops_1 @ B @ A ) <=>
% 7.24/7.43             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 7.24/7.43  thf('17', plain,
% 7.24/7.43      (![X31 : $i, X32 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.24/7.43          | ~ (v1_tops_1 @ X31 @ X32)
% 7.24/7.43          | ((k2_pre_topc @ X32 @ X31) = (k2_struct_0 @ X32))
% 7.24/7.43          | ~ (l1_pre_topc @ X32))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_tops_1])).
% 7.24/7.43  thf('18', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 7.24/7.43          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['16', '17'])).
% 7.24/7.43  thf('19', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('20', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['14', '15'])).
% 7.24/7.43  thf(t48_pre_topc, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 7.24/7.43  thf('21', plain,
% 7.24/7.43      (![X24 : $i, X25 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 7.24/7.43          | (r1_tarski @ X24 @ (k2_pre_topc @ X25 @ X24))
% 7.24/7.43          | ~ (l1_pre_topc @ X25))),
% 7.24/7.43      inference('cnf', [status(esa)], [t48_pre_topc])).
% 7.24/7.43  thf('22', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 7.24/7.43             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 7.24/7.43      inference('sup-', [status(thm)], ['20', '21'])).
% 7.24/7.43  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['14', '15'])).
% 7.24/7.43  thf('24', plain,
% 7.24/7.43      (![X21 : $i, X22 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X21)
% 7.24/7.43          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 7.24/7.43          | (m1_subset_1 @ (k2_pre_topc @ X21 @ X22) @ 
% 7.24/7.43             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.24/7.43  thf('25', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 7.24/7.43           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['23', '24'])).
% 7.24/7.43  thf('26', plain,
% 7.24/7.43      (![X17 : $i, X18 : $i]:
% 7.24/7.43         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('27', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 7.24/7.43             (u1_struct_0 @ X0)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['25', '26'])).
% 7.24/7.43  thf('28', plain,
% 7.24/7.43      (![X0 : $i, X2 : $i]:
% 7.24/7.43         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.24/7.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.24/7.43  thf('29', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 7.24/7.43               (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.24/7.43          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 7.24/7.43      inference('sup-', [status(thm)], ['27', '28'])).
% 7.24/7.43  thf('30', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['22', '29'])).
% 7.24/7.43  thf('31', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('simplify', [status(thm)], ['30'])).
% 7.24/7.43  thf('32', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['14', '15'])).
% 7.24/7.43  thf('33', plain,
% 7.24/7.43      (![X31 : $i, X32 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.24/7.43          | ((k2_pre_topc @ X32 @ X31) != (k2_struct_0 @ X32))
% 7.24/7.43          | (v1_tops_1 @ X31 @ X32)
% 7.24/7.43          | ~ (l1_pre_topc @ X32))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_tops_1])).
% 7.24/7.43  thf('34', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 7.24/7.43          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['32', '33'])).
% 7.24/7.43  thf('35', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (((u1_struct_0 @ X0) != (k2_struct_0 @ X0))
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['31', '34'])).
% 7.24/7.43  thf('36', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | ((u1_struct_0 @ X0) != (k2_struct_0 @ X0)))),
% 7.24/7.43      inference('simplify', [status(thm)], ['35'])).
% 7.24/7.43  thf('37', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 7.24/7.43          | ~ (l1_struct_0 @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['19', '36'])).
% 7.24/7.43  thf('38', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | ~ (l1_struct_0 @ X0))),
% 7.24/7.43      inference('simplify', [status(thm)], ['37'])).
% 7.24/7.43  thf('39', plain,
% 7.24/7.43      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 7.24/7.43  thf('40', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 7.24/7.43      inference('clc', [status(thm)], ['38', '39'])).
% 7.24/7.43  thf('41', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('clc', [status(thm)], ['18', '40'])).
% 7.24/7.43  thf('42', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 7.24/7.43             (u1_struct_0 @ X0)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['25', '26'])).
% 7.24/7.43  thf('43', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         ((r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('sup+', [status(thm)], ['41', '42'])).
% 7.24/7.43  thf('44', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0)
% 7.24/7.43          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 7.24/7.43      inference('simplify', [status(thm)], ['43'])).
% 7.24/7.43  thf('45', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('46', plain,
% 7.24/7.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('47', plain,
% 7.24/7.43      (![X17 : $i, X18 : $i]:
% 7.24/7.43         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('48', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['46', '47'])).
% 7.24/7.43  thf('49', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['14', '15'])).
% 7.24/7.43  thf('50', plain,
% 7.24/7.43      (![X7 : $i, X8 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 7.24/7.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.24/7.43  thf('51', plain,
% 7.24/7.43      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['49', '50'])).
% 7.24/7.43  thf('52', plain,
% 7.24/7.43      (![X17 : $i, X18 : $i]:
% 7.24/7.43         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('53', plain, (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 7.24/7.43      inference('sup-', [status(thm)], ['51', '52'])).
% 7.24/7.43  thf(t1_xboole_1, axiom,
% 7.24/7.43    (![A:$i,B:$i,C:$i]:
% 7.24/7.43     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 7.24/7.43       ( r1_tarski @ A @ C ) ))).
% 7.24/7.43  thf('54', plain,
% 7.24/7.43      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.24/7.43         (~ (r1_tarski @ X3 @ X4)
% 7.24/7.43          | ~ (r1_tarski @ X4 @ X5)
% 7.24/7.43          | (r1_tarski @ X3 @ X5))),
% 7.24/7.43      inference('cnf', [status(esa)], [t1_xboole_1])).
% 7.24/7.43  thf('55', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1) | ~ (r1_tarski @ X0 @ X1))),
% 7.24/7.43      inference('sup-', [status(thm)], ['53', '54'])).
% 7.24/7.43  thf('56', plain,
% 7.24/7.43      ((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['48', '55'])).
% 7.24/7.43  thf('57', plain,
% 7.24/7.43      (![X17 : $i, X19 : $i]:
% 7.24/7.43         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('58', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['56', '57'])).
% 7.24/7.43  thf('59', plain,
% 7.24/7.43      (![X7 : $i, X8 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 7.24/7.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.24/7.43  thf('60', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['58', '59'])).
% 7.24/7.43  thf('61', plain,
% 7.24/7.43      (![X17 : $i, X18 : $i]:
% 7.24/7.43         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('62', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 7.24/7.43        (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['60', '61'])).
% 7.24/7.43  thf('63', plain,
% 7.24/7.43      (((r1_tarski @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 7.24/7.43         (k2_struct_0 @ sk_A))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['45', '62'])).
% 7.24/7.43  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('65', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 7.24/7.43        (k2_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['63', '64'])).
% 7.24/7.43  thf('66', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('67', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['1', '2'])).
% 7.24/7.43  thf('68', plain,
% 7.24/7.43      (![X17 : $i, X18 : $i]:
% 7.24/7.43         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('69', plain,
% 7.24/7.43      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['67', '68'])).
% 7.24/7.43  thf('70', plain,
% 7.24/7.43      (((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43         (u1_struct_0 @ sk_A))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['66', '69'])).
% 7.24/7.43  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('72', plain,
% 7.24/7.43      ((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['70', '71'])).
% 7.24/7.43  thf('73', plain,
% 7.24/7.43      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['49', '50'])).
% 7.24/7.43  thf(t35_subset_1, axiom,
% 7.24/7.43    (![A:$i,B:$i]:
% 7.24/7.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.43       ( ![C:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.43           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 7.24/7.43             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 7.24/7.43  thf('74', plain,
% 7.24/7.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 7.24/7.43          | (r1_tarski @ X11 @ (k3_subset_1 @ X12 @ X13))
% 7.24/7.43          | ~ (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 7.24/7.43          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t35_subset_1])).
% 7.24/7.43  thf('75', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 7.24/7.43          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)))
% 7.24/7.43          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['73', '74'])).
% 7.24/7.43  thf('76', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['14', '15'])).
% 7.24/7.43  thf(involutiveness_k3_subset_1, axiom,
% 7.24/7.43    (![A:$i,B:$i]:
% 7.24/7.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.43       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 7.24/7.43  thf('77', plain,
% 7.24/7.43      (![X9 : $i, X10 : $i]:
% 7.24/7.43         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 7.24/7.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 7.24/7.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.24/7.43  thf('78', plain,
% 7.24/7.43      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['76', '77'])).
% 7.24/7.43  thf('79', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 7.24/7.43          | ~ (r1_tarski @ X1 @ X0)
% 7.24/7.43          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1)))),
% 7.24/7.43      inference('demod', [status(thm)], ['75', '78'])).
% 7.24/7.43  thf('80', plain,
% 7.24/7.43      (![X17 : $i, X19 : $i]:
% 7.24/7.43         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('81', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 7.24/7.43          | ~ (r1_tarski @ X1 @ X0))),
% 7.24/7.43      inference('clc', [status(thm)], ['79', '80'])).
% 7.24/7.43  thf('82', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['72', '81'])).
% 7.24/7.43  thf('83', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('84', plain,
% 7.24/7.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('85', plain,
% 7.24/7.43      (![X9 : $i, X10 : $i]:
% 7.24/7.43         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 7.24/7.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 7.24/7.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.24/7.43  thf('86', plain,
% 7.24/7.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.24/7.43      inference('sup-', [status(thm)], ['84', '85'])).
% 7.24/7.43  thf('87', plain,
% 7.24/7.43      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['83', '86'])).
% 7.24/7.43  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('89', plain,
% 7.24/7.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.24/7.43      inference('demod', [status(thm)], ['87', '88'])).
% 7.24/7.43  thf('90', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)),
% 7.24/7.43      inference('demod', [status(thm)], ['82', '89'])).
% 7.24/7.43  thf('91', plain,
% 7.24/7.43      (![X17 : $i, X19 : $i]:
% 7.24/7.43         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('92', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ sk_B))),
% 7.24/7.43      inference('sup-', [status(thm)], ['90', '91'])).
% 7.24/7.43  thf('93', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['14', '15'])).
% 7.24/7.43  thf(t36_subset_1, axiom,
% 7.24/7.43    (![A:$i,B:$i]:
% 7.24/7.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.43       ( ![C:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.43           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 7.24/7.43             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 7.24/7.43  thf('94', plain,
% 7.24/7.43      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 7.24/7.43          | (r1_tarski @ (k3_subset_1 @ X15 @ X14) @ X16)
% 7.24/7.43          | ~ (r1_tarski @ (k3_subset_1 @ X15 @ X16) @ X14)
% 7.24/7.43          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t36_subset_1])).
% 7.24/7.43  thf('95', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 7.24/7.43          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 7.24/7.43          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 7.24/7.43      inference('sup-', [status(thm)], ['93', '94'])).
% 7.24/7.43  thf('96', plain,
% 7.24/7.43      (((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 7.24/7.43        | ~ (r1_tarski @ 
% 7.24/7.43             (k3_subset_1 @ sk_B @ 
% 7.24/7.43              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 7.24/7.43             sk_B))),
% 7.24/7.43      inference('sup-', [status(thm)], ['92', '95'])).
% 7.24/7.43  thf('97', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ sk_B))),
% 7.24/7.43      inference('sup-', [status(thm)], ['90', '91'])).
% 7.24/7.43  thf('98', plain,
% 7.24/7.43      (![X7 : $i, X8 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 7.24/7.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.24/7.43  thf('99', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k3_subset_1 @ sk_B @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 7.24/7.43        (k1_zfmisc_1 @ sk_B))),
% 7.24/7.43      inference('sup-', [status(thm)], ['97', '98'])).
% 7.24/7.43  thf('100', plain,
% 7.24/7.43      (![X17 : $i, X18 : $i]:
% 7.24/7.43         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('101', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ sk_B @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 7.24/7.43        sk_B)),
% 7.24/7.43      inference('sup-', [status(thm)], ['99', '100'])).
% 7.24/7.43  thf('102', plain,
% 7.24/7.43      ((r1_tarski @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['96', '101'])).
% 7.24/7.43  thf('103', plain,
% 7.24/7.43      (![X0 : $i, X2 : $i]:
% 7.24/7.43         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.24/7.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.24/7.43  thf('104', plain,
% 7.24/7.43      ((~ (r1_tarski @ 
% 7.24/7.43           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 7.24/7.43           (k3_subset_1 @ sk_B @ sk_B))
% 7.24/7.43        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.24/7.43            = (k3_subset_1 @ sk_B @ sk_B)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['102', '103'])).
% 7.24/7.43  thf('105', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)) @ 
% 7.24/7.43        (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['60', '61'])).
% 7.24/7.43  thf('106', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 7.24/7.43          | ~ (r1_tarski @ X1 @ X0))),
% 7.24/7.43      inference('clc', [status(thm)], ['79', '80'])).
% 7.24/7.43  thf('107', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B))))),
% 7.24/7.43      inference('sup-', [status(thm)], ['105', '106'])).
% 7.24/7.43  thf('108', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['56', '57'])).
% 7.24/7.43  thf('109', plain,
% 7.24/7.43      (![X9 : $i, X10 : $i]:
% 7.24/7.43         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 7.24/7.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 7.24/7.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.24/7.43  thf('110', plain,
% 7.24/7.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B)))
% 7.24/7.43         = (k3_subset_1 @ sk_B @ sk_B))),
% 7.24/7.43      inference('sup-', [status(thm)], ['108', '109'])).
% 7.24/7.43  thf('111', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 7.24/7.43        (k3_subset_1 @ sk_B @ sk_B))),
% 7.24/7.43      inference('demod', [status(thm)], ['107', '110'])).
% 7.24/7.43  thf('112', plain,
% 7.24/7.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.24/7.43         = (k3_subset_1 @ sk_B @ sk_B))),
% 7.24/7.43      inference('demod', [status(thm)], ['104', '111'])).
% 7.24/7.43  thf('113', plain,
% 7.24/7.43      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['76', '77'])).
% 7.24/7.43  thf('114', plain,
% 7.24/7.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B))
% 7.24/7.43         = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['112', '113'])).
% 7.24/7.43  thf('115', plain,
% 7.24/7.43      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['65', '114'])).
% 7.24/7.43  thf('116', plain,
% 7.24/7.43      (![X0 : $i, X2 : $i]:
% 7.24/7.43         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.24/7.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.24/7.43  thf('117', plain,
% 7.24/7.43      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.24/7.43        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['115', '116'])).
% 7.24/7.43  thf('118', plain,
% 7.24/7.43      ((~ (l1_pre_topc @ sk_A) | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['44', '117'])).
% 7.24/7.43  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('120', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['118', '119'])).
% 7.24/7.43  thf('121', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['12', '120'])).
% 7.24/7.43  thf('122', plain,
% 7.24/7.43      (![X17 : $i, X18 : $i]:
% 7.24/7.43         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.24/7.43      inference('cnf', [status(esa)], [t3_subset])).
% 7.24/7.43  thf('123', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43        (k2_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['121', '122'])).
% 7.24/7.43  thf('124', plain,
% 7.24/7.43      (![X0 : $i, X2 : $i]:
% 7.24/7.43         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.24/7.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.24/7.43  thf('125', plain,
% 7.24/7.43      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 7.24/7.43           (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 7.24/7.43        | ((k2_struct_0 @ sk_A)
% 7.24/7.43            = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 7.24/7.43      inference('sup-', [status(thm)], ['123', '124'])).
% 7.24/7.43  thf('126', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('127', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['1', '2'])).
% 7.24/7.43  thf('128', plain,
% 7.24/7.43      (![X31 : $i, X32 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.24/7.43          | ((k2_pre_topc @ X32 @ X31) != (k2_struct_0 @ X32))
% 7.24/7.43          | (v1_tops_1 @ X31 @ X32)
% 7.24/7.43          | ~ (l1_pre_topc @ X32))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_tops_1])).
% 7.24/7.43  thf('129', plain,
% 7.24/7.43      ((~ (l1_pre_topc @ sk_A)
% 7.24/7.43        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 7.24/7.43        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43            != (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['127', '128'])).
% 7.24/7.43  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('131', plain,
% 7.24/7.43      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 7.24/7.43        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43            != (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['129', '130'])).
% 7.24/7.43  thf('132', plain,
% 7.24/7.43      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('133', plain,
% 7.24/7.43      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43         != (k2_struct_0 @ sk_A))),
% 7.24/7.43      inference('clc', [status(thm)], ['131', '132'])).
% 7.24/7.43  thf('134', plain,
% 7.24/7.43      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43          != (k2_struct_0 @ sk_A))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['126', '133'])).
% 7.24/7.43  thf('135', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('136', plain,
% 7.24/7.43      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43         != (k2_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['134', '135'])).
% 7.24/7.43  thf('137', plain,
% 7.24/7.43      (~ (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 7.24/7.43          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 7.24/7.43      inference('simplify_reflect-', [status(thm)], ['125', '136'])).
% 7.24/7.43  thf('138', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['1', '2'])).
% 7.24/7.43  thf(t44_tops_1, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 7.24/7.43  thf('139', plain,
% 7.24/7.43      (![X37 : $i, X38 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.24/7.43          | (r1_tarski @ (k1_tops_1 @ X38 @ X37) @ X37)
% 7.24/7.43          | ~ (l1_pre_topc @ X38))),
% 7.24/7.43      inference('cnf', [status(esa)], [t44_tops_1])).
% 7.24/7.43  thf('140', plain,
% 7.24/7.43      ((~ (l1_pre_topc @ sk_A)
% 7.24/7.43        | (r1_tarski @ 
% 7.24/7.43           (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['138', '139'])).
% 7.24/7.43  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('142', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 7.24/7.43      inference('demod', [status(thm)], ['140', '141'])).
% 7.24/7.43  thf('143', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['118', '119'])).
% 7.24/7.43  thf('144', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['118', '119'])).
% 7.24/7.43  thf('145', plain,
% 7.24/7.43      ((r1_tarski @ 
% 7.24/7.43        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43        (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 7.24/7.43      inference('demod', [status(thm)], ['142', '143', '144'])).
% 7.24/7.43  thf('146', plain,
% 7.24/7.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('147', plain,
% 7.24/7.43      (![X21 : $i, X22 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X21)
% 7.24/7.43          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 7.24/7.43          | (m1_subset_1 @ (k2_pre_topc @ X21 @ X22) @ 
% 7.24/7.43             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.24/7.43  thf('148', plain,
% 7.24/7.43      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.24/7.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.24/7.43        | ~ (l1_pre_topc @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['146', '147'])).
% 7.24/7.43  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('150', plain,
% 7.24/7.43      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['148', '149'])).
% 7.24/7.43  thf('151', plain,
% 7.24/7.43      (![X7 : $i, X8 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 7.24/7.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.24/7.43  thf('152', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['150', '151'])).
% 7.24/7.43  thf('153', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['1', '2'])).
% 7.24/7.43  thf(d1_tops_1, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( ( k1_tops_1 @ A @ B ) =
% 7.24/7.43             ( k3_subset_1 @
% 7.24/7.43               ( u1_struct_0 @ A ) @ 
% 7.24/7.43               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 7.24/7.43  thf('154', plain,
% 7.24/7.43      (![X29 : $i, X30 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 7.24/7.43          | ((k1_tops_1 @ X30 @ X29)
% 7.24/7.43              = (k3_subset_1 @ (u1_struct_0 @ X30) @ 
% 7.24/7.43                 (k2_pre_topc @ X30 @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29))))
% 7.24/7.43          | ~ (l1_pre_topc @ X30))),
% 7.24/7.43      inference('cnf', [status(esa)], [d1_tops_1])).
% 7.24/7.43  thf('155', plain,
% 7.24/7.43      ((~ (l1_pre_topc @ sk_A)
% 7.24/7.43        | ((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43               (k2_pre_topc @ sk_A @ 
% 7.24/7.43                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 7.24/7.43      inference('sup-', [status(thm)], ['153', '154'])).
% 7.24/7.43  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('157', plain,
% 7.24/7.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.24/7.43      inference('sup-', [status(thm)], ['84', '85'])).
% 7.24/7.43  thf('158', plain,
% 7.24/7.43      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.24/7.43      inference('demod', [status(thm)], ['155', '156', '157'])).
% 7.24/7.43  thf('159', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['152', '158'])).
% 7.24/7.43  thf(t49_pre_topc, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( ![C:$i]:
% 7.24/7.43             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43               ( ( r1_tarski @ B @ C ) =>
% 7.24/7.43                 ( r1_tarski @
% 7.24/7.43                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 7.24/7.43  thf('160', plain,
% 7.24/7.43      (![X26 : $i, X27 : $i, X28 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 7.24/7.43          | ~ (r1_tarski @ X26 @ X28)
% 7.24/7.43          | (r1_tarski @ (k2_pre_topc @ X27 @ X26) @ (k2_pre_topc @ X27 @ X28))
% 7.24/7.43          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 7.24/7.43          | ~ (l1_pre_topc @ X27))),
% 7.24/7.43      inference('cnf', [status(esa)], [t49_pre_topc])).
% 7.24/7.43  thf('161', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ sk_A)
% 7.24/7.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.24/7.43          | (r1_tarski @ 
% 7.24/7.43             (k2_pre_topc @ sk_A @ 
% 7.24/7.43              (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 7.24/7.43             (k2_pre_topc @ sk_A @ X0))
% 7.24/7.43          | ~ (r1_tarski @ 
% 7.24/7.43               (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43               X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['159', '160'])).
% 7.24/7.43  thf('162', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('163', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.24/7.43          | (r1_tarski @ 
% 7.24/7.43             (k2_pre_topc @ sk_A @ 
% 7.24/7.43              (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 7.24/7.43             (k2_pre_topc @ sk_A @ X0))
% 7.24/7.43          | ~ (r1_tarski @ 
% 7.24/7.43               (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43               X0))),
% 7.24/7.43      inference('demod', [status(thm)], ['161', '162'])).
% 7.24/7.43  thf('164', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['118', '119'])).
% 7.24/7.43  thf('165', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['118', '119'])).
% 7.24/7.43  thf('166', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('167', plain,
% 7.24/7.43      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['148', '149'])).
% 7.24/7.43  thf('168', plain,
% 7.24/7.43      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.24/7.43         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['166', '167'])).
% 7.24/7.43  thf('169', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('170', plain,
% 7.24/7.43      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['168', '169'])).
% 7.24/7.43  thf('171', plain,
% 7.24/7.43      (![X7 : $i, X8 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 7.24/7.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.24/7.43  thf('172', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['170', '171'])).
% 7.24/7.43  thf('173', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('174', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['4', '7'])).
% 7.24/7.43  thf('175', plain,
% 7.24/7.43      (![X29 : $i, X30 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 7.24/7.43          | ((k1_tops_1 @ X30 @ X29)
% 7.24/7.43              = (k3_subset_1 @ (u1_struct_0 @ X30) @ 
% 7.24/7.43                 (k2_pre_topc @ X30 @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29))))
% 7.24/7.43          | ~ (l1_pre_topc @ X30))),
% 7.24/7.43      inference('cnf', [status(esa)], [d1_tops_1])).
% 7.24/7.43  thf('176', plain,
% 7.24/7.43      ((~ (l1_pre_topc @ sk_A)
% 7.24/7.43        | ((k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43               (k2_pre_topc @ sk_A @ 
% 7.24/7.43                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43                 (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))))),
% 7.24/7.43      inference('sup-', [status(thm)], ['174', '175'])).
% 7.24/7.43  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('178', plain,
% 7.24/7.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.24/7.43         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.24/7.43      inference('demod', [status(thm)], ['87', '88'])).
% 7.24/7.43  thf('179', plain,
% 7.24/7.43      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.24/7.43      inference('demod', [status(thm)], ['176', '177', '178'])).
% 7.24/7.43  thf('180', plain,
% 7.24/7.43      ((((k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['173', '179'])).
% 7.24/7.43  thf('181', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('182', plain,
% 7.24/7.43      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.24/7.43      inference('demod', [status(thm)], ['180', '181'])).
% 7.24/7.43  thf('183', plain,
% 7.24/7.43      ((m1_subset_1 @ 
% 7.24/7.43        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['172', '182'])).
% 7.24/7.43  thf('184', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['118', '119'])).
% 7.24/7.43  thf('185', plain,
% 7.24/7.43      (![X31 : $i, X32 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.24/7.43          | ~ (v1_tops_1 @ X31 @ X32)
% 7.24/7.43          | ((k2_pre_topc @ X32 @ X31) = (k2_struct_0 @ X32))
% 7.24/7.43          | ~ (l1_pre_topc @ X32))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_tops_1])).
% 7.24/7.43  thf('186', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.24/7.43          | ~ (l1_pre_topc @ sk_A)
% 7.24/7.43          | ((k2_pre_topc @ sk_A @ X0) = (k2_struct_0 @ sk_A))
% 7.24/7.43          | ~ (v1_tops_1 @ X0 @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['184', '185'])).
% 7.24/7.43  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('188', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.24/7.43          | ((k2_pre_topc @ sk_A @ X0) = (k2_struct_0 @ sk_A))
% 7.24/7.43          | ~ (v1_tops_1 @ X0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['186', '187'])).
% 7.24/7.43  thf('189', plain,
% 7.24/7.43      ((~ (v1_tops_1 @ 
% 7.24/7.43           (k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43           sk_A)
% 7.24/7.43        | ((k2_pre_topc @ sk_A @ 
% 7.24/7.43            (k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 7.24/7.43            = (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['183', '188'])).
% 7.24/7.43  thf('190', plain,
% 7.24/7.43      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['168', '169'])).
% 7.24/7.43  thf('191', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('simplify', [status(thm)], ['30'])).
% 7.24/7.43  thf('192', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('clc', [status(thm)], ['18', '40'])).
% 7.24/7.43  thf('193', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0))),
% 7.24/7.43      inference('sup+', [status(thm)], ['191', '192'])).
% 7.24/7.43  thf('194', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 7.24/7.43      inference('simplify', [status(thm)], ['193'])).
% 7.24/7.43  thf(d4_tops_1, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( ( v2_tops_1 @ B @ A ) <=>
% 7.24/7.43             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 7.24/7.43  thf('195', plain,
% 7.24/7.43      (![X33 : $i, X34 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 7.24/7.43          | ~ (v2_tops_1 @ X33 @ X34)
% 7.24/7.43          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33) @ X34)
% 7.24/7.43          | ~ (l1_pre_topc @ X34))),
% 7.24/7.43      inference('cnf', [status(esa)], [d4_tops_1])).
% 7.24/7.43  thf('196', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 7.24/7.43          | ~ (v2_tops_1 @ X1 @ X0))),
% 7.24/7.43      inference('sup-', [status(thm)], ['194', '195'])).
% 7.24/7.43  thf('197', plain,
% 7.24/7.43      (![X0 : $i, X1 : $i]:
% 7.24/7.43         (~ (v2_tops_1 @ X1 @ X0)
% 7.24/7.43          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 7.24/7.43          | ~ (l1_pre_topc @ X0)
% 7.24/7.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 7.24/7.43      inference('simplify', [status(thm)], ['196'])).
% 7.24/7.43  thf('198', plain,
% 7.24/7.43      ((~ (l1_pre_topc @ sk_A)
% 7.24/7.43        | (v1_tops_1 @ 
% 7.24/7.43           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.24/7.43           sk_A)
% 7.24/7.43        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['190', '197'])).
% 7.24/7.43  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('200', plain,
% 7.24/7.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf(d5_tops_1, axiom,
% 7.24/7.43    (![A:$i]:
% 7.24/7.43     ( ( l1_pre_topc @ A ) =>
% 7.24/7.43       ( ![B:$i]:
% 7.24/7.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.24/7.43           ( ( v3_tops_1 @ B @ A ) <=>
% 7.24/7.43             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 7.24/7.43  thf('201', plain,
% 7.24/7.43      (![X35 : $i, X36 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.24/7.43          | ~ (v3_tops_1 @ X35 @ X36)
% 7.24/7.43          | (v2_tops_1 @ (k2_pre_topc @ X36 @ X35) @ X36)
% 7.24/7.43          | ~ (l1_pre_topc @ X36))),
% 7.24/7.43      inference('cnf', [status(esa)], [d5_tops_1])).
% 7.24/7.43  thf('202', plain,
% 7.24/7.43      ((~ (l1_pre_topc @ sk_A)
% 7.24/7.43        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 7.24/7.43        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 7.24/7.43      inference('sup-', [status(thm)], ['200', '201'])).
% 7.24/7.43  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('204', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('205', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 7.24/7.43      inference('demod', [status(thm)], ['202', '203', '204'])).
% 7.24/7.43  thf('206', plain,
% 7.24/7.43      ((v1_tops_1 @ 
% 7.24/7.43        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.24/7.43        sk_A)),
% 7.24/7.43      inference('demod', [status(thm)], ['198', '199', '205'])).
% 7.24/7.43  thf('207', plain,
% 7.24/7.43      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 7.24/7.43         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.24/7.43      inference('demod', [status(thm)], ['176', '177', '178'])).
% 7.24/7.43  thf('208', plain,
% 7.24/7.43      ((v1_tops_1 @ 
% 7.24/7.43        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ sk_A)),
% 7.24/7.43      inference('demod', [status(thm)], ['206', '207'])).
% 7.24/7.43  thf('209', plain,
% 7.24/7.43      (((k2_pre_topc @ sk_A @ 
% 7.24/7.43         (k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 7.24/7.43         = (k2_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['189', '208'])).
% 7.24/7.43  thf('210', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.24/7.43      inference('demod', [status(thm)], ['118', '119'])).
% 7.24/7.43  thf('211', plain,
% 7.24/7.43      (![X0 : $i]:
% 7.24/7.43         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.24/7.43          | (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 7.24/7.43          | ~ (r1_tarski @ 
% 7.24/7.43               (k1_tops_1 @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 7.24/7.43               X0))),
% 7.24/7.43      inference('demod', [status(thm)], ['163', '164', '165', '209', '210'])).
% 7.24/7.43  thf('212', plain,
% 7.24/7.43      (((r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 7.24/7.43         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 7.24/7.43        | ~ (m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 7.24/7.43      inference('sup-', [status(thm)], ['145', '211'])).
% 7.24/7.43  thf('213', plain,
% 7.24/7.43      (![X20 : $i]:
% 7.24/7.43         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 7.24/7.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.24/7.43  thf('214', plain,
% 7.24/7.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.24/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.43  thf('215', plain,
% 7.24/7.43      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.24/7.43        | ~ (l1_struct_0 @ sk_A))),
% 7.24/7.43      inference('sup+', [status(thm)], ['213', '214'])).
% 7.24/7.43  thf('216', plain, ((l1_struct_0 @ sk_A)),
% 7.24/7.43      inference('sup-', [status(thm)], ['5', '6'])).
% 7.24/7.43  thf('217', plain,
% 7.24/7.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('demod', [status(thm)], ['215', '216'])).
% 7.24/7.43  thf('218', plain,
% 7.24/7.43      (![X7 : $i, X8 : $i]:
% 7.24/7.43         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 7.24/7.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 7.24/7.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.24/7.43  thf('219', plain,
% 7.24/7.43      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 7.24/7.43        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.24/7.43      inference('sup-', [status(thm)], ['217', '218'])).
% 7.24/7.43  thf('220', plain,
% 7.24/7.43      ((r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 7.24/7.43        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 7.24/7.43      inference('demod', [status(thm)], ['212', '219'])).
% 7.24/7.43  thf('221', plain, ($false), inference('demod', [status(thm)], ['137', '220'])).
% 7.24/7.43  
% 7.24/7.43  % SZS output end Refutation
% 7.24/7.43  
% 7.24/7.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
