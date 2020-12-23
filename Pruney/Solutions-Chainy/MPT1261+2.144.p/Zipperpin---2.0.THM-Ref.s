%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YbUX8e0O6f

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:59 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 226 expanded)
%              Number of leaves         :   30 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  864 (2979 expanded)
%              Number of equality atoms :   57 ( 165 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( k2_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
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

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('44',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','47'])).

thf('49',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['13','50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['11','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X29 @ X28 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ ( k2_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('59',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['53','61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['13','50'])).

thf('67',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YbUX8e0O6f
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 254 iterations in 0.114s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(t77_tops_1, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.57             ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.57               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57          ( ![B:$i]:
% 0.36/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57              ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.57                ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.57                  ( k7_subset_1 @
% 0.36/0.57                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t69_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v4_pre_topc @ B @ A ) =>
% 0.36/0.57             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X26 : $i, X27 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.36/0.57          | (r1_tarski @ (k2_tops_1 @ X27 @ X26) @ X26)
% 0.36/0.57          | ~ (v4_pre_topc @ X26 @ X27)
% 0.36/0.57          | ~ (l1_pre_topc @ X27))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.57  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['1', '6'])).
% 0.36/0.57  thf(t28_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.36/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57              (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (~
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.57       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('split', [status(esa)], ['12'])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t65_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.36/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X24 : $i, X25 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.36/0.57          | ((k2_pre_topc @ X25 @ X24)
% 0.36/0.57              = (k4_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 0.36/0.57                 (k2_tops_1 @ X25 @ X24)))
% 0.36/0.57          | ~ (l1_pre_topc @ X25))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(dt_k2_tops_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.57       ( m1_subset_1 @
% 0.36/0.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (![X20 : $i, X21 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X20)
% 0.36/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.57          | (m1_subset_1 @ (k2_tops_1 @ X20 @ X21) @ 
% 0.36/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.57  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.36/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.36/0.57          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.57  thf('26', plain,
% 0.36/0.57      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.57  thf('27', plain,
% 0.36/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['16', '17', '26'])).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.36/0.57          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf(t36_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.36/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.57  thf(t22_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (![X4 : $i, X5 : $i]:
% 0.36/0.57         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.36/0.57      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['32', '39'])).
% 0.36/0.57  thf('41', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['27', '40'])).
% 0.36/0.57  thf('42', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(fc1_tops_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.57       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X22 : $i, X23 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X22)
% 0.36/0.57          | ~ (v2_pre_topc @ X22)
% 0.36/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.57          | (v4_pre_topc @ (k2_pre_topc @ X22 @ X23) @ X22))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.36/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.57  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('47', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['41', '47'])).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['12'])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.57       ~
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('52', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['13', '50', '51'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['11', '52'])).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t74_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( k1_tops_1 @ A @ B ) =
% 0.36/0.57             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.36/0.57          | ((k1_tops_1 @ X29 @ X28)
% 0.36/0.57              = (k7_subset_1 @ (u1_struct_0 @ X29) @ X28 @ 
% 0.36/0.57                 (k2_tops_1 @ X29 @ X28)))
% 0.36/0.57          | ~ (l1_pre_topc @ X29))),
% 0.36/0.57      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.57  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.57  thf('59', plain,
% 0.36/0.57      (((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.57         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.36/0.57  thf(t48_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.36/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.57  thf('61', plain,
% 0.36/0.57      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.36/0.57  thf('62', plain,
% 0.36/0.57      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('sup+', [status(thm)], ['53', '61'])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57              (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (~
% 0.36/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('split', [status(esa)], ['12'])).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.57  thf('65', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (~
% 0.36/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['63', '64'])).
% 0.36/0.57  thf('66', plain,
% 0.36/0.57      (~
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['13', '50'])).
% 0.36/0.57  thf('67', plain,
% 0.36/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.36/0.57  thf('68', plain, ($false),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['62', '67'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
