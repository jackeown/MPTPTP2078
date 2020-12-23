%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CbnO9Q1abh

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:36 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 531 expanded)
%              Number of leaves         :   42 ( 171 expanded)
%              Depth                    :   15
%              Number of atoms          : 1825 (6774 expanded)
%              Number of equality atoms :  137 ( 416 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X39 @ X38 ) @ X38 )
      | ~ ( v4_pre_topc @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k1_tops_1 @ X41 @ X40 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( k2_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('38',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','38'])).

thf('40',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','39'])).

thf('41',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('43',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','54'])).

thf('56',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['40','57'])).

thf('59',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('71',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('73',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('85',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('91',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('99',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','103'])).

thf('105',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('107',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
        = ( k2_subset_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('108',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('109',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('113',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('115',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('117',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('119',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('121',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['116','121'])).

thf('123',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['115','122'])).

thf('124',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','123'])).

thf('125',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['105','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('127',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X34 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('128',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['125','131'])).

thf('133',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','69','70','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CbnO9Q1abh
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:48:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.98/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.17  % Solved by: fo/fo7.sh
% 0.98/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.17  % done 1185 iterations in 0.711s
% 0.98/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.17  % SZS output start Refutation
% 0.98/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.98/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.17  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.98/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.17  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.98/1.17  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.98/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.98/1.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.98/1.17  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.98/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.98/1.17  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.98/1.17  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.98/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.98/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.98/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.98/1.17  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.98/1.17  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.98/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(t77_tops_1, conjecture,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.98/1.17       ( ![B:$i]:
% 0.98/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.17           ( ( v4_pre_topc @ B @ A ) <=>
% 0.98/1.17             ( ( k2_tops_1 @ A @ B ) =
% 0.98/1.17               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.98/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.17    (~( ![A:$i]:
% 0.98/1.17        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.98/1.17          ( ![B:$i]:
% 0.98/1.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.17              ( ( v4_pre_topc @ B @ A ) <=>
% 0.98/1.17                ( ( k2_tops_1 @ A @ B ) =
% 0.98/1.17                  ( k7_subset_1 @
% 0.98/1.17                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.98/1.17    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.98/1.17  thf('0', plain,
% 0.98/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.17          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.17              (k1_tops_1 @ sk_A @ sk_B)))
% 0.98/1.17        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('1', plain,
% 0.98/1.17      (~
% 0.98/1.17       (((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.17             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.98/1.17       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.98/1.17      inference('split', [status(esa)], ['0'])).
% 0.98/1.17  thf('2', plain,
% 0.98/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.17             (k1_tops_1 @ sk_A @ sk_B)))
% 0.98/1.17        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('3', plain,
% 0.98/1.17      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('split', [status(esa)], ['2'])).
% 0.98/1.17  thf('4', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(t69_tops_1, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( l1_pre_topc @ A ) =>
% 0.98/1.17       ( ![B:$i]:
% 0.98/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.17           ( ( v4_pre_topc @ B @ A ) =>
% 0.98/1.17             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.98/1.17  thf('5', plain,
% 0.98/1.17      (![X38 : $i, X39 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.98/1.17          | (r1_tarski @ (k2_tops_1 @ X39 @ X38) @ X38)
% 0.98/1.17          | ~ (v4_pre_topc @ X38 @ X39)
% 0.98/1.17          | ~ (l1_pre_topc @ X39))),
% 0.98/1.17      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.98/1.17  thf('6', plain,
% 0.98/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.98/1.17        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.98/1.17        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.98/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.98/1.17  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('8', plain,
% 0.98/1.17      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.98/1.17        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.98/1.17      inference('demod', [status(thm)], ['6', '7'])).
% 0.98/1.17  thf('9', plain,
% 0.98/1.17      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['3', '8'])).
% 0.98/1.17  thf(t3_subset, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.98/1.17  thf('10', plain,
% 0.98/1.17      (![X29 : $i, X31 : $i]:
% 0.98/1.17         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X29 @ X31))),
% 0.98/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.98/1.17  thf('11', plain,
% 0.98/1.17      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['9', '10'])).
% 0.98/1.17  thf(involutiveness_k3_subset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.17       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.98/1.17  thf('12', plain,
% 0.98/1.17      (![X17 : $i, X18 : $i]:
% 0.98/1.17         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 0.98/1.17          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.98/1.17      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.98/1.17  thf('13', plain,
% 0.98/1.17      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.98/1.17          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['11', '12'])).
% 0.98/1.17  thf('14', plain,
% 0.98/1.17      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['9', '10'])).
% 0.98/1.17  thf(d5_subset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.17       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.98/1.17  thf('15', plain,
% 0.98/1.17      (![X13 : $i, X14 : $i]:
% 0.98/1.17         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.98/1.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.98/1.17      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.98/1.17  thf('16', plain,
% 0.98/1.17      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.17          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['14', '15'])).
% 0.98/1.17  thf('17', plain,
% 0.98/1.17      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['3', '8'])).
% 0.98/1.17  thf(t28_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.98/1.17  thf('18', plain,
% 0.98/1.17      (![X4 : $i, X5 : $i]:
% 0.98/1.17         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.98/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.98/1.17  thf('19', plain,
% 0.98/1.17      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.98/1.17          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['17', '18'])).
% 0.98/1.17  thf(commutativity_k2_tarski, axiom,
% 0.98/1.17    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.98/1.17  thf('20', plain,
% 0.98/1.17      (![X10 : $i, X11 : $i]:
% 0.98/1.17         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.98/1.17      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.98/1.17  thf(t12_setfam_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.98/1.17  thf('21', plain,
% 0.98/1.17      (![X27 : $i, X28 : $i]:
% 0.98/1.17         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.98/1.17      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.98/1.17  thf('22', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('sup+', [status(thm)], ['20', '21'])).
% 0.98/1.17  thf('23', plain,
% 0.98/1.17      (![X27 : $i, X28 : $i]:
% 0.98/1.17         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.98/1.17      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.98/1.17  thf('24', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('sup+', [status(thm)], ['22', '23'])).
% 0.98/1.17  thf('25', plain,
% 0.98/1.17      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.17          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('demod', [status(thm)], ['19', '24'])).
% 0.98/1.17  thf(t100_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.98/1.17  thf('26', plain,
% 0.98/1.17      (![X2 : $i, X3 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ X2 @ X3)
% 0.98/1.17           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.98/1.17  thf('27', plain,
% 0.98/1.17      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.17          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['25', '26'])).
% 0.98/1.17  thf('28', plain,
% 0.98/1.17      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.17          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.17      inference('demod', [status(thm)], ['16', '27'])).
% 0.98/1.17  thf('29', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(t74_tops_1, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( l1_pre_topc @ A ) =>
% 0.98/1.17       ( ![B:$i]:
% 0.98/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.17           ( ( k1_tops_1 @ A @ B ) =
% 0.98/1.17             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.98/1.17  thf('30', plain,
% 0.98/1.17      (![X40 : $i, X41 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.98/1.17          | ((k1_tops_1 @ X41 @ X40)
% 0.98/1.17              = (k7_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 0.98/1.17                 (k2_tops_1 @ X41 @ X40)))
% 0.98/1.17          | ~ (l1_pre_topc @ X41))),
% 0.98/1.17      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.98/1.17  thf('31', plain,
% 0.98/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.98/1.17        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.17            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.17               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.98/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.98/1.17  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('33', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(redefinition_k7_subset_1, axiom,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.18       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.98/1.18  thf('34', plain,
% 0.98/1.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.98/1.18         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.98/1.18          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.98/1.18  thf('35', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_B @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['33', '34'])).
% 0.98/1.18  thf('36', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf('37', plain,
% 0.98/1.18      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['25', '26'])).
% 0.98/1.18  thf('38', plain,
% 0.98/1.18      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['36', '37'])).
% 0.98/1.18  thf('39', plain,
% 0.98/1.18      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.98/1.18         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.18      inference('demod', [status(thm)], ['28', '38'])).
% 0.98/1.18  thf('40', plain,
% 0.98/1.18      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.98/1.18         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.18      inference('demod', [status(thm)], ['13', '39'])).
% 0.98/1.18  thf('41', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf(t36_xboole_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.98/1.18  thf('42', plain,
% 0.98/1.18      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.98/1.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.98/1.18  thf('43', plain,
% 0.98/1.18      (![X29 : $i, X31 : $i]:
% 0.98/1.18         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X29 @ X31))),
% 0.98/1.18      inference('cnf', [status(esa)], [t3_subset])).
% 0.98/1.18  thf('44', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['42', '43'])).
% 0.98/1.18  thf('45', plain,
% 0.98/1.18      (![X13 : $i, X14 : $i]:
% 0.98/1.18         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.98/1.18          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.98/1.18      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.98/1.18  thf('46', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.98/1.18           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['44', '45'])).
% 0.98/1.18  thf('47', plain,
% 0.98/1.18      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.98/1.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.98/1.18  thf('48', plain,
% 0.98/1.18      (![X4 : $i, X5 : $i]:
% 0.98/1.18         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.98/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.98/1.18  thf('49', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.98/1.18           = (k4_xboole_0 @ X0 @ X1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['47', '48'])).
% 0.98/1.18  thf('50', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.98/1.18      inference('sup+', [status(thm)], ['22', '23'])).
% 0.98/1.18  thf('51', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.98/1.18           = (k4_xboole_0 @ X0 @ X1))),
% 0.98/1.18      inference('demod', [status(thm)], ['49', '50'])).
% 0.98/1.18  thf('52', plain,
% 0.98/1.18      (![X2 : $i, X3 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ X2 @ X3)
% 0.98/1.18           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.98/1.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.98/1.18  thf('53', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.98/1.18           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['51', '52'])).
% 0.98/1.18  thf('54', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.98/1.18           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.98/1.18      inference('demod', [status(thm)], ['46', '53'])).
% 0.98/1.18  thf('55', plain,
% 0.98/1.18      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k5_xboole_0 @ sk_B @ 
% 0.98/1.18            (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['41', '54'])).
% 0.98/1.18  thf('56', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf('57', plain,
% 0.98/1.18      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['55', '56'])).
% 0.98/1.18  thf('58', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['40', '57'])).
% 0.98/1.18  thf('59', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf('60', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.98/1.18           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['51', '52'])).
% 0.98/1.18  thf('61', plain,
% 0.98/1.18      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k5_xboole_0 @ sk_B @ 
% 0.98/1.18            (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['59', '60'])).
% 0.98/1.18  thf('62', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf('63', plain,
% 0.98/1.18      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['61', '62'])).
% 0.98/1.18  thf('64', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_B @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['33', '34'])).
% 0.98/1.18  thf('65', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18              (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= (~
% 0.98/1.18             (((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('split', [status(esa)], ['0'])).
% 0.98/1.18  thf('66', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= (~
% 0.98/1.18             (((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['64', '65'])).
% 0.98/1.18  thf('67', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= (~
% 0.98/1.18             (((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['63', '66'])).
% 0.98/1.18  thf('68', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.98/1.18         <= (~
% 0.98/1.18             (((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.98/1.18             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['58', '67'])).
% 0.98/1.18  thf('69', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.98/1.18       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.98/1.18      inference('simplify', [status(thm)], ['68'])).
% 0.98/1.18  thf('70', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.98/1.18       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.98/1.18      inference('split', [status(esa)], ['2'])).
% 0.98/1.18  thf('71', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf('72', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['42', '43'])).
% 0.98/1.18  thf('73', plain,
% 0.98/1.18      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['71', '72'])).
% 0.98/1.18  thf('74', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_B @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['33', '34'])).
% 0.98/1.18  thf('75', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18             (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('split', [status(esa)], ['2'])).
% 0.98/1.18  thf('76', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['74', '75'])).
% 0.98/1.18  thf('77', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['42', '43'])).
% 0.98/1.18  thf('78', plain,
% 0.98/1.18      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['76', '77'])).
% 0.98/1.18  thf(redefinition_k4_subset_1, axiom,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.98/1.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.98/1.18       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.98/1.18  thf('79', plain,
% 0.98/1.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.98/1.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.98/1.18          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.98/1.18          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.98/1.18  thf('80', plain,
% 0.98/1.18      ((![X0 : $i]:
% 0.98/1.18          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.98/1.18             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.98/1.18           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['78', '79'])).
% 0.98/1.18  thf('81', plain,
% 0.98/1.18      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.98/1.18          (k1_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.98/1.18             (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['73', '80'])).
% 0.98/1.18  thf(commutativity_k2_xboole_0, axiom,
% 0.98/1.18    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.98/1.18  thf('82', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.98/1.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.98/1.18  thf('83', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf(t39_xboole_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]:
% 0.98/1.18     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.98/1.18  thf('84', plain,
% 0.98/1.18      (![X8 : $i, X9 : $i]:
% 0.98/1.18         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.98/1.18           = (k2_xboole_0 @ X8 @ X9))),
% 0.98/1.18      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.98/1.18  thf('85', plain,
% 0.98/1.18      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['83', '84'])).
% 0.98/1.18  thf('86', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.98/1.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.98/1.18  thf('87', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.98/1.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.98/1.18  thf('88', plain,
% 0.98/1.18      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.98/1.18  thf('89', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(dt_k2_tops_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]:
% 0.98/1.18     ( ( ( l1_pre_topc @ A ) & 
% 0.98/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.18       ( m1_subset_1 @
% 0.98/1.18         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.98/1.18  thf('90', plain,
% 0.98/1.18      (![X32 : $i, X33 : $i]:
% 0.98/1.18         (~ (l1_pre_topc @ X32)
% 0.98/1.18          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.98/1.18          | (m1_subset_1 @ (k2_tops_1 @ X32 @ X33) @ 
% 0.98/1.18             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.98/1.18      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.98/1.18  thf('91', plain,
% 0.98/1.18      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.98/1.18         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['89', '90'])).
% 0.98/1.18  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('93', plain,
% 0.98/1.18      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.98/1.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.18      inference('demod', [status(thm)], ['91', '92'])).
% 0.98/1.18  thf('94', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('95', plain,
% 0.98/1.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.98/1.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.98/1.18          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.98/1.18          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.98/1.18  thf('96', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.98/1.18            = (k2_xboole_0 @ sk_B @ X0))
% 0.98/1.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['94', '95'])).
% 0.98/1.18  thf('97', plain,
% 0.98/1.18      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['93', '96'])).
% 0.98/1.18  thf('98', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(t65_tops_1, axiom,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ( l1_pre_topc @ A ) =>
% 0.98/1.18       ( ![B:$i]:
% 0.98/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.18           ( ( k2_pre_topc @ A @ B ) =
% 0.98/1.18             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.98/1.18  thf('99', plain,
% 0.98/1.18      (![X36 : $i, X37 : $i]:
% 0.98/1.18         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.98/1.18          | ((k2_pre_topc @ X37 @ X36)
% 0.98/1.18              = (k4_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.98/1.18                 (k2_tops_1 @ X37 @ X36)))
% 0.98/1.18          | ~ (l1_pre_topc @ X37))),
% 0.98/1.18      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.98/1.18  thf('100', plain,
% 0.98/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.98/1.18        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.98/1.18            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['98', '99'])).
% 0.98/1.18  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('102', plain,
% 0.98/1.18      (((k2_pre_topc @ sk_A @ sk_B)
% 0.98/1.18         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['100', '101'])).
% 0.98/1.18  thf('103', plain,
% 0.98/1.18      (((k2_pre_topc @ sk_A @ sk_B)
% 0.98/1.18         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['97', '102'])).
% 0.98/1.18  thf('104', plain,
% 0.98/1.18      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.98/1.18      inference('demod', [status(thm)], ['88', '103'])).
% 0.98/1.18  thf('105', plain,
% 0.98/1.18      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.98/1.18          (k1_tops_1 @ sk_A @ sk_B)) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('demod', [status(thm)], ['81', '82', '104'])).
% 0.98/1.18  thf('106', plain,
% 0.98/1.18      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['76', '77'])).
% 0.98/1.18  thf(t25_subset_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]:
% 0.98/1.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.18       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.98/1.18         ( k2_subset_1 @ A ) ) ))).
% 0.98/1.18  thf('107', plain,
% 0.98/1.18      (![X25 : $i, X26 : $i]:
% 0.98/1.18         (((k4_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X26))
% 0.98/1.18            = (k2_subset_1 @ X25))
% 0.98/1.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.98/1.18      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.98/1.18  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.98/1.18  thf('108', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.98/1.18      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.98/1.18  thf('109', plain,
% 0.98/1.18      (![X25 : $i, X26 : $i]:
% 0.98/1.18         (((k4_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X26)) = (X25))
% 0.98/1.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.98/1.18      inference('demod', [status(thm)], ['107', '108'])).
% 0.98/1.18  thf('110', plain,
% 0.98/1.18      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.98/1.18          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['106', '109'])).
% 0.98/1.18  thf('111', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['74', '75'])).
% 0.98/1.18  thf('112', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.98/1.18           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.98/1.18      inference('demod', [status(thm)], ['46', '53'])).
% 0.98/1.18  thf('113', plain,
% 0.98/1.18      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ 
% 0.98/1.18             (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['111', '112'])).
% 0.98/1.18  thf('114', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['74', '75'])).
% 0.98/1.18  thf('115', plain,
% 0.98/1.18      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('demod', [status(thm)], ['113', '114'])).
% 0.98/1.18  thf('116', plain,
% 0.98/1.18      (((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.98/1.18  thf('117', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['74', '75'])).
% 0.98/1.18  thf('118', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.98/1.18           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['51', '52'])).
% 0.98/1.18  thf('119', plain,
% 0.98/1.18      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ 
% 0.98/1.18             (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['117', '118'])).
% 0.98/1.18  thf('120', plain,
% 0.98/1.18      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['74', '75'])).
% 0.98/1.18  thf('121', plain,
% 0.98/1.18      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('demod', [status(thm)], ['119', '120'])).
% 0.98/1.18  thf('122', plain,
% 0.98/1.18      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['116', '121'])).
% 0.98/1.18  thf('123', plain,
% 0.98/1.18      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.98/1.18          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('demod', [status(thm)], ['115', '122'])).
% 0.98/1.18  thf('124', plain,
% 0.98/1.18      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.98/1.18          (k1_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('demod', [status(thm)], ['110', '123'])).
% 0.98/1.18  thf('125', plain,
% 0.98/1.18      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['105', '124'])).
% 0.98/1.18  thf('126', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(fc1_tops_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]:
% 0.98/1.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.98/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.18       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.98/1.18  thf('127', plain,
% 0.98/1.18      (![X34 : $i, X35 : $i]:
% 0.98/1.18         (~ (l1_pre_topc @ X34)
% 0.98/1.18          | ~ (v2_pre_topc @ X34)
% 0.98/1.18          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.98/1.18          | (v4_pre_topc @ (k2_pre_topc @ X34 @ X35) @ X34))),
% 0.98/1.18      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.98/1.18  thf('128', plain,
% 0.98/1.18      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.98/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.98/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['126', '127'])).
% 0.98/1.18  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('131', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.98/1.18      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.98/1.18  thf('132', plain,
% 0.98/1.18      (((v4_pre_topc @ sk_B @ sk_A))
% 0.98/1.18         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['125', '131'])).
% 0.98/1.18  thf('133', plain,
% 0.98/1.18      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.98/1.18      inference('split', [status(esa)], ['0'])).
% 0.98/1.18  thf('134', plain,
% 0.98/1.18      (~
% 0.98/1.18       (((k2_tops_1 @ sk_A @ sk_B)
% 0.98/1.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.98/1.18             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.98/1.18       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['132', '133'])).
% 0.98/1.18  thf('135', plain, ($false),
% 0.98/1.18      inference('sat_resolution*', [status(thm)], ['1', '69', '70', '134'])).
% 0.98/1.18  
% 0.98/1.18  % SZS output end Refutation
% 0.98/1.18  
% 0.98/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
