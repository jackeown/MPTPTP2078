%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDYkeZjNub

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:52 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 220 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  854 (2929 expanded)
%              Number of equality atoms :   56 ( 159 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X25 @ X24 ) @ X24 )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
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

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('42',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf('47',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('48',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['13','48','49'])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['11','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('57',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['13','48'])).

thf('65',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDYkeZjNub
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:22 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 235 iterations in 0.134s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.41/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.61  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.41/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.41/0.61  thf(t77_tops_1, conjecture,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ( v4_pre_topc @ B @ A ) <=>
% 0.41/0.61             ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.61               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i]:
% 0.41/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61          ( ![B:$i]:
% 0.41/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61              ( ( v4_pre_topc @ B @ A ) <=>
% 0.41/0.61                ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.61                  ( k7_subset_1 @
% 0.41/0.61                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61             (k1_tops_1 @ sk_A @ sk_B)))
% 0.41/0.61        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t69_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ( v4_pre_topc @ B @ A ) =>
% 0.41/0.61             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | (r1_tarski @ (k2_tops_1 @ X25 @ X24) @ X24)
% 0.41/0.61          | ~ (v4_pre_topc @ X24 @ X25)
% 0.41/0.61          | ~ (l1_pre_topc @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.41/0.61        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.41/0.61        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.41/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '6'])).
% 0.41/0.61  thf(t28_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i]:
% 0.41/0.61         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.41/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61              (k1_tops_1 @ sk_A @ sk_B)))
% 0.41/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (~
% 0.41/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.41/0.61       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t65_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ( k2_pre_topc @ A @ B ) =
% 0.41/0.61             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.61          | ((k2_pre_topc @ X23 @ X22)
% 0.41/0.61              = (k4_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.41/0.61                 (k2_tops_1 @ X23 @ X22)))
% 0.41/0.61          | ~ (l1_pre_topc @ X23))),
% 0.41/0.61      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.61            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_k2_tops_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.61       ( m1_subset_1 @
% 0.41/0.61         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X18)
% 0.41/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.61          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.41/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.61  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(redefinition_k4_subset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.41/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.41/0.61          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.61            = (k2_xboole_0 @ sk_B @ X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '25'])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['16', '17', '26'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(redefinition_k7_subset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.61       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.41/0.61          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61             (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['30', '31'])).
% 0.41/0.61  thf(t36_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.41/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.41/0.61  thf(t12_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.41/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['32', '37'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.41/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['27', '38'])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(fc1_tops_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.41/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.61       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X20 : $i, X21 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X20)
% 0.41/0.61          | ~ (v2_pre_topc @ X20)
% 0.41/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.61          | (v4_pre_topc @ (k2_pre_topc @ X20 @ X21) @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.41/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.61  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('45', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.41/0.61      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (((v4_pre_topc @ sk_B @ sk_A))
% 0.41/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['39', '45'])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.41/0.61       ~
% 0.41/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.41/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('50', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['13', '48', '49'])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.61         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['11', '50'])).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t74_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ( k1_tops_1 @ A @ B ) =
% 0.41/0.61             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (![X26 : $i, X27 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.61          | ((k1_tops_1 @ X27 @ X26)
% 0.41/0.61              = (k7_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.41/0.61                 (k2_tops_1 @ X27 @ X26)))
% 0.41/0.61          | ~ (l1_pre_topc @ X27))),
% 0.41/0.61      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.41/0.61            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      (((k1_tops_1 @ sk_A @ sk_B)
% 0.41/0.61         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.41/0.61  thf(t48_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.41/0.61           = (k3_xboole_0 @ X10 @ X11))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.41/0.61         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['57', '58'])).
% 0.41/0.61  thf('60', plain,
% 0.41/0.61      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.41/0.61         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.41/0.61      inference('sup+', [status(thm)], ['51', '59'])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61              (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.61         <= (~
% 0.41/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.61         <= (~
% 0.41/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.61      inference('demod', [status(thm)], ['61', '62'])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      (~
% 0.41/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.61             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['13', '48'])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.61         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['63', '64'])).
% 0.41/0.61  thf('66', plain, ($false),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['60', '65'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
