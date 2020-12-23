%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HVwqJwmTbj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:01 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 448 expanded)
%              Number of leaves         :   37 ( 140 expanded)
%              Depth                    :   17
%              Number of atoms          : 1179 (5837 expanded)
%              Number of equality atoms :   85 ( 349 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','60'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('64',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X29 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('65',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','68'])).

thf('70',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['19','71','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','73'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('77',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('81',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['75','81'])).

thf('83',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['19','71','72'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['74','84'])).

thf('86',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['19','71'])).

thf('90',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HVwqJwmTbj
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:01:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.53/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.76  % Solved by: fo/fo7.sh
% 0.53/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.76  % done 1086 iterations in 0.303s
% 0.53/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.76  % SZS output start Refutation
% 0.53/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.76  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.53/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.76  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.53/0.76  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.53/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.76  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.53/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.53/0.76  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.53/0.76  thf(t77_tops_1, conjecture,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.76           ( ( v4_pre_topc @ B @ A ) <=>
% 0.53/0.76             ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.76               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.53/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.76    (~( ![A:$i]:
% 0.53/0.76        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.76          ( ![B:$i]:
% 0.53/0.76            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.76              ( ( v4_pre_topc @ B @ A ) <=>
% 0.53/0.76                ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.76                  ( k7_subset_1 @
% 0.53/0.76                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.53/0.76    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.53/0.76  thf('0', plain,
% 0.53/0.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76             (k1_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('1', plain,
% 0.53/0.76      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('split', [status(esa)], ['0'])).
% 0.53/0.76  thf('2', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t69_tops_1, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( l1_pre_topc @ A ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.76           ( ( v4_pre_topc @ B @ A ) =>
% 0.53/0.76             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.53/0.76  thf('3', plain,
% 0.53/0.76      (![X33 : $i, X34 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.53/0.76          | (r1_tarski @ (k2_tops_1 @ X34 @ X33) @ X33)
% 0.53/0.76          | ~ (v4_pre_topc @ X33 @ X34)
% 0.53/0.76          | ~ (l1_pre_topc @ X34))),
% 0.53/0.76      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.53/0.76  thf('4', plain,
% 0.53/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.76        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.53/0.76        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.53/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.76  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('6', plain,
% 0.53/0.76      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.53/0.76        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.53/0.76      inference('demod', [status(thm)], ['4', '5'])).
% 0.53/0.76  thf('7', plain,
% 0.53/0.76      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['1', '6'])).
% 0.53/0.76  thf(t28_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.76  thf('8', plain,
% 0.53/0.76      (![X10 : $i, X11 : $i]:
% 0.53/0.76         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.53/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.76  thf('9', plain,
% 0.53/0.76      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.53/0.76          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.76  thf('10', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.76  thf('11', plain,
% 0.53/0.76      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.76          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.53/0.76  thf(t100_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.76  thf('12', plain,
% 0.53/0.76      (![X5 : $i, X6 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.76           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.76  thf('13', plain,
% 0.53/0.76      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.76          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.76  thf(t48_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.76  thf('14', plain,
% 0.53/0.76      (![X16 : $i, X17 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.53/0.76           = (k3_xboole_0 @ X16 @ X17))),
% 0.53/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.76  thf('15', plain,
% 0.53/0.76      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.53/0.76  thf('16', plain,
% 0.53/0.76      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.76          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.53/0.76  thf('17', plain,
% 0.53/0.76      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('demod', [status(thm)], ['15', '16'])).
% 0.53/0.76  thf('18', plain,
% 0.53/0.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76              (k1_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('19', plain,
% 0.53/0.76      (~
% 0.53/0.76       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.53/0.76       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.76      inference('split', [status(esa)], ['18'])).
% 0.53/0.76  thf('20', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t65_tops_1, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( l1_pre_topc @ A ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.76           ( ( k2_pre_topc @ A @ B ) =
% 0.53/0.76             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.53/0.76  thf('21', plain,
% 0.53/0.76      (![X31 : $i, X32 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.53/0.76          | ((k2_pre_topc @ X32 @ X31)
% 0.53/0.76              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.53/0.76                 (k2_tops_1 @ X32 @ X31)))
% 0.53/0.76          | ~ (l1_pre_topc @ X32))),
% 0.53/0.76      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.53/0.76  thf('22', plain,
% 0.53/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.76        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.76            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.53/0.76  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('24', plain,
% 0.53/0.76      (((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.76         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.53/0.76  thf('25', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t3_subset, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.76  thf('26', plain,
% 0.53/0.76      (![X26 : $i, X27 : $i]:
% 0.53/0.76         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.76  thf('27', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.76      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.76  thf('28', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(redefinition_k7_subset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.76       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.53/0.76  thf('29', plain,
% 0.53/0.76      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.53/0.76          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.53/0.76  thf('30', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.76           = (k4_xboole_0 @ sk_B @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.76  thf('31', plain,
% 0.53/0.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76             (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('split', [status(esa)], ['0'])).
% 0.53/0.76  thf('32', plain,
% 0.53/0.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.76  thf(t36_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.76  thf('33', plain,
% 0.53/0.76      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.76  thf('34', plain,
% 0.53/0.76      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['32', '33'])).
% 0.53/0.76  thf(t1_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.53/0.76       ( r1_tarski @ A @ C ) ))).
% 0.53/0.76  thf('35', plain,
% 0.53/0.76      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.76         (~ (r1_tarski @ X7 @ X8)
% 0.53/0.76          | ~ (r1_tarski @ X8 @ X9)
% 0.53/0.76          | (r1_tarski @ X7 @ X9))),
% 0.53/0.76      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.53/0.76  thf('36', plain,
% 0.53/0.76      ((![X0 : $i]:
% 0.53/0.76          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.53/0.76           | ~ (r1_tarski @ sk_B @ X0)))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.76  thf('37', plain,
% 0.53/0.76      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['27', '36'])).
% 0.53/0.76  thf('38', plain,
% 0.53/0.76      (![X26 : $i, X28 : $i]:
% 0.53/0.76         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 0.53/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.76  thf('39', plain,
% 0.53/0.76      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['37', '38'])).
% 0.53/0.76  thf('40', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(redefinition_k4_subset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.53/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.53/0.76       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.76  thf('41', plain,
% 0.53/0.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.53/0.76          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.53/0.76          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.53/0.76  thf('42', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.76            = (k2_xboole_0 @ sk_B @ X0))
% 0.53/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['40', '41'])).
% 0.53/0.76  thf('43', plain,
% 0.53/0.76      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.76          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['39', '42'])).
% 0.53/0.76  thf('44', plain,
% 0.53/0.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.76  thf('45', plain,
% 0.53/0.76      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.76  thf(l32_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.76  thf('46', plain,
% 0.53/0.76      (![X2 : $i, X4 : $i]:
% 0.53/0.76         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.53/0.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.76  thf('47', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.76  thf('48', plain,
% 0.53/0.76      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['44', '47'])).
% 0.53/0.76  thf(t98_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.53/0.76  thf('49', plain,
% 0.53/0.76      (![X18 : $i, X19 : $i]:
% 0.53/0.76         ((k2_xboole_0 @ X18 @ X19)
% 0.53/0.76           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.53/0.76  thf('50', plain,
% 0.53/0.76      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.76          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['48', '49'])).
% 0.53/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.53/0.76  thf('51', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.53/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.76  thf('52', plain,
% 0.53/0.76      (![X10 : $i, X11 : $i]:
% 0.53/0.76         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.53/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.76  thf('53', plain,
% 0.53/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.53/0.76  thf('54', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.76  thf('55', plain,
% 0.53/0.76      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['53', '54'])).
% 0.53/0.76  thf('56', plain,
% 0.53/0.76      (![X5 : $i, X6 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.76           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.76  thf('57', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['55', '56'])).
% 0.53/0.76  thf(t3_boole, axiom,
% 0.53/0.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.76  thf('58', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.53/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.76  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['57', '58'])).
% 0.53/0.76  thf('60', plain,
% 0.53/0.76      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('demod', [status(thm)], ['50', '59'])).
% 0.53/0.76  thf('61', plain,
% 0.53/0.76      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.76          = (sk_B)))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('demod', [status(thm)], ['43', '60'])).
% 0.53/0.76  thf('62', plain,
% 0.53/0.76      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['24', '61'])).
% 0.53/0.76  thf('63', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(fc1_tops_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.53/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.76       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.53/0.76  thf('64', plain,
% 0.53/0.76      (![X29 : $i, X30 : $i]:
% 0.53/0.76         (~ (l1_pre_topc @ X29)
% 0.53/0.76          | ~ (v2_pre_topc @ X29)
% 0.53/0.76          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.53/0.76          | (v4_pre_topc @ (k2_pre_topc @ X29 @ X30) @ X29))),
% 0.53/0.76      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.53/0.76  thf('65', plain,
% 0.53/0.76      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.53/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.53/0.76        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.76      inference('sup-', [status(thm)], ['63', '64'])).
% 0.53/0.76  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('68', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.53/0.76      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.53/0.76  thf('69', plain,
% 0.53/0.76      (((v4_pre_topc @ sk_B @ sk_A))
% 0.53/0.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['62', '68'])).
% 0.53/0.76  thf('70', plain,
% 0.53/0.76      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('split', [status(esa)], ['18'])).
% 0.53/0.76  thf('71', plain,
% 0.53/0.76      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.53/0.76       ~
% 0.53/0.76       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['69', '70'])).
% 0.53/0.76  thf('72', plain,
% 0.53/0.76      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.53/0.76       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.76      inference('split', [status(esa)], ['0'])).
% 0.53/0.76  thf('73', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.76      inference('sat_resolution*', [status(thm)], ['19', '71', '72'])).
% 0.53/0.76  thf('74', plain,
% 0.53/0.76      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.76         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.53/0.76      inference('simpl_trail', [status(thm)], ['17', '73'])).
% 0.53/0.76  thf('75', plain,
% 0.53/0.76      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.76          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.76  thf('76', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t74_tops_1, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( l1_pre_topc @ A ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.76           ( ( k1_tops_1 @ A @ B ) =
% 0.53/0.76             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.53/0.76  thf('77', plain,
% 0.53/0.76      (![X35 : $i, X36 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.53/0.76          | ((k1_tops_1 @ X36 @ X35)
% 0.53/0.76              = (k7_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.53/0.76                 (k2_tops_1 @ X36 @ X35)))
% 0.53/0.76          | ~ (l1_pre_topc @ X36))),
% 0.53/0.76      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.53/0.76  thf('78', plain,
% 0.53/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.76        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.76            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['76', '77'])).
% 0.53/0.76  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('80', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.76           = (k4_xboole_0 @ sk_B @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.76  thf('81', plain,
% 0.53/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.76         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.53/0.76  thf('82', plain,
% 0.53/0.76      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['75', '81'])).
% 0.53/0.76  thf('83', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.76      inference('sat_resolution*', [status(thm)], ['19', '71', '72'])).
% 0.53/0.76  thf('84', plain,
% 0.53/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.76         = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.53/0.76  thf('85', plain,
% 0.53/0.76      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.53/0.76         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.53/0.76      inference('demod', [status(thm)], ['74', '84'])).
% 0.53/0.76  thf('86', plain,
% 0.53/0.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76              (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= (~
% 0.53/0.76             (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('split', [status(esa)], ['18'])).
% 0.53/0.76  thf('87', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.76           = (k4_xboole_0 @ sk_B @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.76  thf('88', plain,
% 0.53/0.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.76         <= (~
% 0.53/0.76             (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.76      inference('demod', [status(thm)], ['86', '87'])).
% 0.53/0.76  thf('89', plain,
% 0.53/0.76      (~
% 0.53/0.76       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.76             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.76      inference('sat_resolution*', [status(thm)], ['19', '71'])).
% 0.53/0.76  thf('90', plain,
% 0.53/0.76      (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.76         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 0.53/0.76  thf('91', plain, ($false),
% 0.53/0.76      inference('simplify_reflect-', [status(thm)], ['85', '90'])).
% 0.53/0.76  
% 0.53/0.76  % SZS output end Refutation
% 0.53/0.76  
% 0.53/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
