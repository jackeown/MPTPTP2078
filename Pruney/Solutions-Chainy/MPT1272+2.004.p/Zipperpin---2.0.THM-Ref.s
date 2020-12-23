%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ygi7CPaAHt

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:28 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 161 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  812 (1630 expanded)
%              Number of equality atoms :   32 (  34 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tops_1 @ X20 @ X21 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ X26 ) @ ( k1_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X10 @ X12 )
        = ( k4_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','31'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ X18 @ ( k2_pre_topc @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('55',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_tops_1 @ X31 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_tops_1 @ X22 @ X23 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X23 @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','64'])).

thf('66',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','53','65'])).

thf('67',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','66'])).

thf('68',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','67'])).

thf('69',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['6','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ygi7CPaAHt
% 0.13/0.37  % Computer   : n003.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:59:57 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.96/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.96/1.17  % Solved by: fo/fo7.sh
% 0.96/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.17  % done 1183 iterations in 0.693s
% 0.96/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.96/1.17  % SZS output start Refutation
% 0.96/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.96/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.96/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.96/1.17  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.96/1.17  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.96/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.17  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.96/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.96/1.17  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.96/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.17  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.96/1.17  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.96/1.17  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.96/1.17  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.96/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.96/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.96/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.96/1.17  thf(t91_tops_1, conjecture,
% 0.96/1.17    (![A:$i]:
% 0.96/1.17     ( ( l1_pre_topc @ A ) =>
% 0.96/1.17       ( ![B:$i]:
% 0.96/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.17           ( ( v3_tops_1 @ B @ A ) =>
% 0.96/1.17             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.96/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.17    (~( ![A:$i]:
% 0.96/1.17        ( ( l1_pre_topc @ A ) =>
% 0.96/1.17          ( ![B:$i]:
% 0.96/1.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.17              ( ( v3_tops_1 @ B @ A ) =>
% 0.96/1.17                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.96/1.17    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 0.96/1.17  thf('0', plain,
% 0.96/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.17  thf(d4_tops_1, axiom,
% 0.96/1.17    (![A:$i]:
% 0.96/1.17     ( ( l1_pre_topc @ A ) =>
% 0.96/1.17       ( ![B:$i]:
% 0.96/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.17           ( ( v2_tops_1 @ B @ A ) <=>
% 0.96/1.17             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.96/1.17  thf('1', plain,
% 0.96/1.17      (![X20 : $i, X21 : $i]:
% 0.96/1.17         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.96/1.17          | ~ (v2_tops_1 @ X20 @ X21)
% 0.96/1.17          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.96/1.17          | ~ (l1_pre_topc @ X21))),
% 0.96/1.17      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.96/1.17  thf('2', plain,
% 0.96/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.96/1.17        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.96/1.17        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.96/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.96/1.17  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.17  thf('4', plain,
% 0.96/1.17      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.96/1.17        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.96/1.17      inference('demod', [status(thm)], ['2', '3'])).
% 0.96/1.17  thf('5', plain,
% 0.96/1.17      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.96/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.17  thf('6', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 0.96/1.17      inference('clc', [status(thm)], ['4', '5'])).
% 0.96/1.17  thf('7', plain,
% 0.96/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.17  thf(t84_tops_1, axiom,
% 0.96/1.17    (![A:$i]:
% 0.96/1.17     ( ( l1_pre_topc @ A ) =>
% 0.96/1.17       ( ![B:$i]:
% 0.96/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.17           ( ( v2_tops_1 @ B @ A ) <=>
% 0.96/1.17             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.96/1.17  thf('8', plain,
% 0.96/1.17      (![X31 : $i, X32 : $i]:
% 0.96/1.17         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.96/1.17          | ((k1_tops_1 @ X32 @ X31) != (k1_xboole_0))
% 0.96/1.17          | (v2_tops_1 @ X31 @ X32)
% 0.96/1.17          | ~ (l1_pre_topc @ X32))),
% 0.96/1.17      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.96/1.17  thf('9', plain,
% 0.96/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.96/1.17        | (v2_tops_1 @ sk_B @ sk_A)
% 0.96/1.17        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.96/1.17      inference('sup-', [status(thm)], ['7', '8'])).
% 0.96/1.17  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.17  thf('11', plain,
% 0.96/1.17      (((v2_tops_1 @ sk_B @ sk_A)
% 0.96/1.17        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.96/1.17      inference('demod', [status(thm)], ['9', '10'])).
% 0.96/1.17  thf('12', plain,
% 0.96/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.17  thf(dt_k2_tops_1, axiom,
% 0.96/1.17    (![A:$i,B:$i]:
% 0.96/1.17     ( ( ( l1_pre_topc @ A ) & 
% 0.96/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.96/1.17       ( m1_subset_1 @
% 0.96/1.17         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.96/1.17  thf('13', plain,
% 0.96/1.17      (![X24 : $i, X25 : $i]:
% 0.96/1.17         (~ (l1_pre_topc @ X24)
% 0.96/1.17          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.96/1.17          | (m1_subset_1 @ (k2_tops_1 @ X24 @ X25) @ 
% 0.96/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.96/1.17      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.96/1.17  thf('14', plain,
% 0.96/1.17      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.96/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.96/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.96/1.17      inference('sup-', [status(thm)], ['12', '13'])).
% 0.96/1.17  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.17  thf('16', plain,
% 0.96/1.17      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.96/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.17      inference('demod', [status(thm)], ['14', '15'])).
% 0.96/1.17  thf(t3_subset, axiom,
% 0.96/1.17    (![A:$i,B:$i]:
% 0.96/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.96/1.17  thf('17', plain,
% 0.96/1.17      (![X13 : $i, X14 : $i]:
% 0.96/1.17         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.96/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.96/1.17  thf('18', plain,
% 0.96/1.17      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.96/1.17      inference('sup-', [status(thm)], ['16', '17'])).
% 0.96/1.17  thf(l32_xboole_1, axiom,
% 0.96/1.17    (![A:$i,B:$i]:
% 0.96/1.17     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.96/1.17  thf('19', plain,
% 0.96/1.17      (![X2 : $i, X4 : $i]:
% 0.96/1.17         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.96/1.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.96/1.18  thf('20', plain,
% 0.96/1.18      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.96/1.18         = (k1_xboole_0))),
% 0.96/1.18      inference('sup-', [status(thm)], ['18', '19'])).
% 0.96/1.18  thf('21', plain,
% 0.96/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf(l78_tops_1, axiom,
% 0.96/1.18    (![A:$i]:
% 0.96/1.18     ( ( l1_pre_topc @ A ) =>
% 0.96/1.18       ( ![B:$i]:
% 0.96/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.18           ( ( k2_tops_1 @ A @ B ) =
% 0.96/1.18             ( k7_subset_1 @
% 0.96/1.18               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.96/1.18               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.96/1.18  thf('22', plain,
% 0.96/1.18      (![X26 : $i, X27 : $i]:
% 0.96/1.18         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.96/1.18          | ((k2_tops_1 @ X27 @ X26)
% 0.96/1.18              = (k7_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.96/1.18                 (k2_pre_topc @ X27 @ X26) @ (k1_tops_1 @ X27 @ X26)))
% 0.96/1.18          | ~ (l1_pre_topc @ X27))),
% 0.96/1.18      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.96/1.18  thf('23', plain,
% 0.96/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.96/1.18        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.96/1.18            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.96/1.18               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.96/1.18      inference('sup-', [status(thm)], ['21', '22'])).
% 0.96/1.18  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf('25', plain,
% 0.96/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf(dt_k2_pre_topc, axiom,
% 0.96/1.18    (![A:$i,B:$i]:
% 0.96/1.18     ( ( ( l1_pre_topc @ A ) & 
% 0.96/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.96/1.18       ( m1_subset_1 @
% 0.96/1.18         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.96/1.18  thf('26', plain,
% 0.96/1.18      (![X16 : $i, X17 : $i]:
% 0.96/1.18         (~ (l1_pre_topc @ X16)
% 0.96/1.18          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.96/1.18          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 0.96/1.18             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.96/1.18      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.96/1.18  thf('27', plain,
% 0.96/1.18      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.96/1.18         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.96/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.96/1.18      inference('sup-', [status(thm)], ['25', '26'])).
% 0.96/1.18  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf('29', plain,
% 0.96/1.18      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.96/1.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('demod', [status(thm)], ['27', '28'])).
% 0.96/1.18  thf(redefinition_k7_subset_1, axiom,
% 0.96/1.18    (![A:$i,B:$i,C:$i]:
% 0.96/1.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.96/1.18       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.96/1.18  thf('30', plain,
% 0.96/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.96/1.18         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.96/1.18          | ((k7_subset_1 @ X11 @ X10 @ X12) = (k4_xboole_0 @ X10 @ X12)))),
% 0.96/1.18      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.96/1.18  thf('31', plain,
% 0.96/1.18      (![X0 : $i]:
% 0.96/1.18         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.96/1.18           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.96/1.18      inference('sup-', [status(thm)], ['29', '30'])).
% 0.96/1.18  thf('32', plain,
% 0.96/1.18      (((k2_tops_1 @ sk_A @ sk_B)
% 0.96/1.18         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.96/1.18            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.96/1.18      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.96/1.18  thf(t41_xboole_1, axiom,
% 0.96/1.18    (![A:$i,B:$i,C:$i]:
% 0.96/1.18     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.96/1.18       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.96/1.18  thf('33', plain,
% 0.96/1.18      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.96/1.18         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.96/1.18           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.96/1.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.96/1.18  thf('34', plain,
% 0.96/1.18      (![X0 : $i]:
% 0.96/1.18         ((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.96/1.18           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.96/1.18              (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))),
% 0.96/1.18      inference('sup+', [status(thm)], ['32', '33'])).
% 0.96/1.18  thf(commutativity_k2_xboole_0, axiom,
% 0.96/1.18    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.96/1.18  thf('35', plain,
% 0.96/1.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.96/1.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.96/1.18  thf('36', plain,
% 0.96/1.18      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.96/1.18         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.96/1.18           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.96/1.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.96/1.18  thf(t38_xboole_1, axiom,
% 0.96/1.18    (![A:$i,B:$i]:
% 0.96/1.18     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.96/1.18       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.96/1.18  thf('37', plain,
% 0.96/1.18      (![X5 : $i, X6 : $i]:
% 0.96/1.18         (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.96/1.18      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.96/1.18  thf('38', plain,
% 0.96/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.18         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.96/1.18          | ((X0) = (k1_xboole_0)))),
% 0.96/1.18      inference('sup-', [status(thm)], ['36', '37'])).
% 0.96/1.18  thf('39', plain,
% 0.96/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.18         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.96/1.18          | ((X1) = (k1_xboole_0)))),
% 0.96/1.18      inference('sup-', [status(thm)], ['35', '38'])).
% 0.96/1.18  thf('40', plain,
% 0.96/1.18      (![X0 : $i]:
% 0.96/1.18         (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.96/1.18             (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.96/1.18          | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.96/1.18      inference('sup-', [status(thm)], ['34', '39'])).
% 0.96/1.18  thf('41', plain,
% 0.96/1.18      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.96/1.18        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.96/1.18      inference('sup-', [status(thm)], ['20', '40'])).
% 0.96/1.18  thf('42', plain,
% 0.96/1.18      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.96/1.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('demod', [status(thm)], ['27', '28'])).
% 0.96/1.18  thf('43', plain,
% 0.96/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf(t48_tops_1, axiom,
% 0.96/1.18    (![A:$i]:
% 0.96/1.18     ( ( l1_pre_topc @ A ) =>
% 0.96/1.18       ( ![B:$i]:
% 0.96/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.18           ( ![C:$i]:
% 0.96/1.18             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.18               ( ( r1_tarski @ B @ C ) =>
% 0.96/1.18                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.96/1.18  thf('44', plain,
% 0.96/1.18      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.96/1.18         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.96/1.18          | ~ (r1_tarski @ X28 @ X30)
% 0.96/1.18          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 0.96/1.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.96/1.18          | ~ (l1_pre_topc @ X29))),
% 0.96/1.18      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.96/1.18  thf('45', plain,
% 0.96/1.18      (![X0 : $i]:
% 0.96/1.18         (~ (l1_pre_topc @ sk_A)
% 0.96/1.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.96/1.18          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.96/1.18          | ~ (r1_tarski @ sk_B @ X0))),
% 0.96/1.18      inference('sup-', [status(thm)], ['43', '44'])).
% 0.96/1.18  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf('47', plain,
% 0.96/1.18      (![X0 : $i]:
% 0.96/1.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.96/1.18          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.96/1.18          | ~ (r1_tarski @ sk_B @ X0))),
% 0.96/1.18      inference('demod', [status(thm)], ['45', '46'])).
% 0.96/1.18  thf('48', plain,
% 0.96/1.18      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.96/1.18        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.96/1.18           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.96/1.18      inference('sup-', [status(thm)], ['42', '47'])).
% 0.96/1.18  thf('49', plain,
% 0.96/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf(t48_pre_topc, axiom,
% 0.96/1.18    (![A:$i]:
% 0.96/1.18     ( ( l1_pre_topc @ A ) =>
% 0.96/1.18       ( ![B:$i]:
% 0.96/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.18           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.96/1.18  thf('50', plain,
% 0.96/1.18      (![X18 : $i, X19 : $i]:
% 0.96/1.18         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.96/1.18          | (r1_tarski @ X18 @ (k2_pre_topc @ X19 @ X18))
% 0.96/1.18          | ~ (l1_pre_topc @ X19))),
% 0.96/1.18      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.96/1.18  thf('51', plain,
% 0.96/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.96/1.18        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.96/1.18      inference('sup-', [status(thm)], ['49', '50'])).
% 0.96/1.18  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf('53', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.96/1.18      inference('demod', [status(thm)], ['51', '52'])).
% 0.96/1.18  thf('54', plain,
% 0.96/1.18      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.96/1.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('demod', [status(thm)], ['27', '28'])).
% 0.96/1.18  thf('55', plain,
% 0.96/1.18      (![X31 : $i, X32 : $i]:
% 0.96/1.18         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.96/1.18          | ~ (v2_tops_1 @ X31 @ X32)
% 0.96/1.18          | ((k1_tops_1 @ X32 @ X31) = (k1_xboole_0))
% 0.96/1.18          | ~ (l1_pre_topc @ X32))),
% 0.96/1.18      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.96/1.18  thf('56', plain,
% 0.96/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.96/1.18        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.96/1.18        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.96/1.18      inference('sup-', [status(thm)], ['54', '55'])).
% 0.96/1.18  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf('58', plain,
% 0.96/1.18      ((((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.96/1.18        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.96/1.18      inference('demod', [status(thm)], ['56', '57'])).
% 0.96/1.18  thf('59', plain,
% 0.96/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf(d5_tops_1, axiom,
% 0.96/1.18    (![A:$i]:
% 0.96/1.18     ( ( l1_pre_topc @ A ) =>
% 0.96/1.18       ( ![B:$i]:
% 0.96/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.18           ( ( v3_tops_1 @ B @ A ) <=>
% 0.96/1.18             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.96/1.18  thf('60', plain,
% 0.96/1.18      (![X22 : $i, X23 : $i]:
% 0.96/1.18         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.96/1.18          | ~ (v3_tops_1 @ X22 @ X23)
% 0.96/1.18          | (v2_tops_1 @ (k2_pre_topc @ X23 @ X22) @ X23)
% 0.96/1.18          | ~ (l1_pre_topc @ X23))),
% 0.96/1.18      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.96/1.18  thf('61', plain,
% 0.96/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.96/1.18        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.96/1.18        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.96/1.18      inference('sup-', [status(thm)], ['59', '60'])).
% 0.96/1.18  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf('63', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.96/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.18  thf('64', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.96/1.18      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.96/1.18  thf('65', plain,
% 0.96/1.18      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.96/1.18      inference('demod', [status(thm)], ['58', '64'])).
% 0.96/1.18  thf('66', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.96/1.18      inference('demod', [status(thm)], ['48', '53', '65'])).
% 0.96/1.18  thf('67', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.96/1.18      inference('demod', [status(thm)], ['41', '66'])).
% 0.96/1.18  thf('68', plain,
% 0.96/1.18      (((v2_tops_1 @ sk_B @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.96/1.18      inference('demod', [status(thm)], ['11', '67'])).
% 0.96/1.18  thf('69', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.96/1.18      inference('simplify', [status(thm)], ['68'])).
% 0.96/1.18  thf('70', plain, ($false), inference('demod', [status(thm)], ['6', '69'])).
% 0.96/1.18  
% 0.96/1.18  % SZS output end Refutation
% 0.96/1.18  
% 0.96/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
