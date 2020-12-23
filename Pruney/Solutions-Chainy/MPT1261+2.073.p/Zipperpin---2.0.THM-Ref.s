%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8xaM3q2DpF

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:48 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 315 expanded)
%              Number of leaves         :   41 ( 112 expanded)
%              Depth                    :   20
%              Number of atoms          : 1375 (3234 expanded)
%              Number of equality atoms :  122 ( 268 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_tops_1 @ X32 @ X31 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k2_pre_topc @ X32 @ X31 ) @ ( k1_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['44','62'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('72',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('76',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('78',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','80'])).

thf('82',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('84',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('85',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('87',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('95',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('96',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('100',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','102'])).

thf('104',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['89','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_pre_topc @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
       != X27 )
      | ( v4_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8xaM3q2DpF
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 328 iterations in 0.142s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.44/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.61  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.44/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.44/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(t77_tops_1, conjecture,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.61             ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.61               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i]:
% 0.44/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.61          ( ![B:$i]:
% 0.44/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61              ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.61                ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.61                  ( k7_subset_1 @
% 0.44/0.61                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.44/0.61  thf('0', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61              (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      (~
% 0.44/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.61       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('split', [status(esa)], ['0'])).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61             (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.61        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.61      inference('split', [status(esa)], ['2'])).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(t52_pre_topc, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_pre_topc @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.44/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.44/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      (![X27 : $i, X28 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.44/0.61          | ~ (v4_pre_topc @ X27 @ X28)
% 0.44/0.61          | ((k2_pre_topc @ X28 @ X27) = (X27))
% 0.44/0.61          | ~ (l1_pre_topc @ X28))),
% 0.44/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.61        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.44/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.61  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.44/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['3', '8'])).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(l78_tops_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_pre_topc @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.61             ( k7_subset_1 @
% 0.44/0.61               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.44/0.61               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.61  thf('11', plain,
% 0.44/0.61      (![X31 : $i, X32 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.44/0.61          | ((k2_tops_1 @ X32 @ X31)
% 0.44/0.61              = (k7_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.44/0.61                 (k2_pre_topc @ X32 @ X31) @ (k1_tops_1 @ X32 @ X31)))
% 0.44/0.61          | ~ (l1_pre_topc @ X32))),
% 0.44/0.61      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.61        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.61               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.61  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('14', plain,
% 0.44/0.61      (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.44/0.61            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61             (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.61      inference('sup+', [status(thm)], ['9', '14'])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_k7_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.61       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.44/0.61          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['15', '18'])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.61  thf('21', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61              (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('split', [status(esa)], ['0'])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.44/0.61             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['19', '22'])).
% 0.44/0.61  thf('24', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.61       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.44/0.61  thf('25', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.61       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('split', [status(esa)], ['2'])).
% 0.44/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.44/0.61  thf('26', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.44/0.61  thf(t100_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X1 : $i, X2 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.44/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.44/0.61  thf(t36_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.44/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.61  thf('30', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.44/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf(t28_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      (![X3 : $i, X4 : $i]:
% 0.44/0.61         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 0.44/0.61           = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.61  thf(commutativity_k2_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      (![X15 : $i, X16 : $i]:
% 0.44/0.61         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.44/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.44/0.61  thf(t12_setfam_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (![X25 : $i, X26 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 0.44/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['33', '34'])).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      (![X25 : $i, X26 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 0.44/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.61  thf('37', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.44/0.61  thf('38', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.44/0.61           = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['32', '37'])).
% 0.44/0.61  thf('39', plain,
% 0.44/0.61      (![X1 : $i, X2 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.44/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.44/0.61           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.44/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.44/0.61  thf(t98_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      (![X13 : $i, X14 : $i]:
% 0.44/0.61         ((k2_xboole_0 @ X13 @ X14)
% 0.44/0.61           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_xboole_0 @ X0 @ X0)
% 0.44/0.61           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.44/0.61      inference('sup+', [status(thm)], ['41', '42'])).
% 0.44/0.61  thf('44', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.44/0.61           = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['40', '43'])).
% 0.44/0.61  thf('45', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.44/0.61           = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['40', '43'])).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.44/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.61  thf('47', plain,
% 0.44/0.61      (![X3 : $i, X4 : $i]:
% 0.44/0.61         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.61  thf('48', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.44/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.61  thf('49', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.44/0.61  thf('50', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.44/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.44/0.61  thf('51', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))
% 0.44/0.61           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.44/0.61      inference('sup+', [status(thm)], ['45', '50'])).
% 0.44/0.61  thf('52', plain,
% 0.44/0.61      (![X15 : $i, X16 : $i]:
% 0.44/0.61         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.44/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.44/0.61  thf(l51_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.61  thf('53', plain,
% 0.44/0.61      (![X17 : $i, X18 : $i]:
% 0.44/0.61         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.61  thf('54', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['52', '53'])).
% 0.44/0.61  thf('55', plain,
% 0.44/0.61      (![X17 : $i, X18 : $i]:
% 0.44/0.61         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.61  thf('56', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.61  thf(t7_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.61  thf('57', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.44/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.61  thf('58', plain,
% 0.44/0.61      (![X3 : $i, X4 : $i]:
% 0.44/0.61         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.61  thf('59', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.61  thf('60', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['56', '59'])).
% 0.44/0.61  thf('61', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.44/0.61           = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['40', '43'])).
% 0.44/0.61  thf('62', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['51', '60', '61'])).
% 0.44/0.61  thf('63', plain,
% 0.44/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['44', '62'])).
% 0.44/0.61  thf(t38_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.44/0.61       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.61  thf('64', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i]:
% 0.44/0.61         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.44/0.61  thf('65', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 0.44/0.61          | ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.61  thf('66', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.44/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.44/0.61  thf('68', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.61  thf('69', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61             (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('split', [status(esa)], ['2'])).
% 0.44/0.61  thf('70', plain,
% 0.44/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['68', '69'])).
% 0.44/0.61  thf('71', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.44/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.61  thf('72', plain,
% 0.44/0.61      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['70', '71'])).
% 0.44/0.61  thf('73', plain,
% 0.44/0.61      (![X3 : $i, X4 : $i]:
% 0.44/0.61         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.61  thf('74', plain,
% 0.44/0.61      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.44/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.44/0.61  thf('75', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.44/0.61  thf('76', plain,
% 0.44/0.61      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.44/0.61  thf('77', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.44/0.61  thf('78', plain,
% 0.44/0.61      (![X1 : $i, X2 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.44/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.61  thf('79', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.61      inference('sup+', [status(thm)], ['77', '78'])).
% 0.44/0.61  thf('80', plain,
% 0.44/0.61      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.44/0.61          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.61             (k2_tops_1 @ sk_A @ sk_B))))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['76', '79'])).
% 0.44/0.61  thf('81', plain,
% 0.44/0.61      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['67', '80'])).
% 0.44/0.61  thf('82', plain,
% 0.44/0.61      (![X13 : $i, X14 : $i]:
% 0.44/0.61         ((k2_xboole_0 @ X13 @ X14)
% 0.44/0.61           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.61  thf('83', plain,
% 0.44/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.61          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['81', '82'])).
% 0.44/0.61  thf(t2_boole, axiom,
% 0.44/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.61  thf('84', plain,
% 0.44/0.61      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.61  thf('85', plain,
% 0.44/0.61      (![X1 : $i, X2 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.44/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.61  thf('86', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['84', '85'])).
% 0.44/0.61  thf(t3_boole, axiom,
% 0.44/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.61  thf('87', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.61  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['86', '87'])).
% 0.44/0.61  thf('89', plain,
% 0.44/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('demod', [status(thm)], ['83', '88'])).
% 0.44/0.61  thf('90', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(t65_tops_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_pre_topc @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( k2_pre_topc @ A @ B ) =
% 0.44/0.61             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.61  thf('91', plain,
% 0.44/0.61      (![X33 : $i, X34 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.44/0.61          | ((k2_pre_topc @ X34 @ X33)
% 0.44/0.61              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.44/0.61                 (k2_tops_1 @ X34 @ X33)))
% 0.44/0.61          | ~ (l1_pre_topc @ X34))),
% 0.44/0.61      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.44/0.61  thf('92', plain,
% 0.44/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.61        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.61            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['90', '91'])).
% 0.44/0.61  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('94', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(dt_k2_tops_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.44/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.61       ( m1_subset_1 @
% 0.44/0.61         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.61  thf('95', plain,
% 0.44/0.61      (![X29 : $i, X30 : $i]:
% 0.44/0.61         (~ (l1_pre_topc @ X29)
% 0.44/0.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.44/0.61          | (m1_subset_1 @ (k2_tops_1 @ X29 @ X30) @ 
% 0.44/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.44/0.61      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.44/0.61  thf('96', plain,
% 0.44/0.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.61  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('98', plain,
% 0.44/0.61      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['96', '97'])).
% 0.44/0.61  thf('99', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_k4_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.44/0.61  thf('100', plain,
% 0.44/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.44/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.44/0.61          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.44/0.61  thf('101', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.61            = (k2_xboole_0 @ sk_B @ X0))
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.44/0.61  thf('102', plain,
% 0.44/0.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['98', '101'])).
% 0.44/0.61  thf('103', plain,
% 0.44/0.61      (((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('demod', [status(thm)], ['92', '93', '102'])).
% 0.44/0.61  thf('104', plain,
% 0.44/0.61      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['89', '103'])).
% 0.44/0.61  thf('105', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('106', plain,
% 0.44/0.61      (![X27 : $i, X28 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.44/0.61          | ~ (v2_pre_topc @ X28)
% 0.44/0.61          | ((k2_pre_topc @ X28 @ X27) != (X27))
% 0.44/0.61          | (v4_pre_topc @ X27 @ X28)
% 0.44/0.61          | ~ (l1_pre_topc @ X28))),
% 0.44/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.44/0.61  thf('107', plain,
% 0.44/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.61        | (v4_pre_topc @ sk_B @ sk_A)
% 0.44/0.61        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.44/0.61        | ~ (v2_pre_topc @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.61  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('110', plain,
% 0.44/0.61      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.44/0.61      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.44/0.61  thf('111', plain,
% 0.44/0.61      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['104', '110'])).
% 0.44/0.61  thf('112', plain,
% 0.44/0.61      (((v4_pre_topc @ sk_B @ sk_A))
% 0.44/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.61      inference('simplify', [status(thm)], ['111'])).
% 0.44/0.61  thf('113', plain,
% 0.44/0.61      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.61      inference('split', [status(esa)], ['0'])).
% 0.44/0.61  thf('114', plain,
% 0.44/0.61      (~
% 0.44/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.61       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['112', '113'])).
% 0.44/0.61  thf('115', plain, ($false),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '114'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
