%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Tanhty0IU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:41 EST 2020

% Result     : Theorem 19.43s
% Output     : Refutation 19.43s
% Verified   : 
% Statistics : Number of formulae       :  325 (4553 expanded)
%              Number of leaves         :   53 (1526 expanded)
%              Depth                    :   24
%              Number of atoms          : 3018 (40789 expanded)
%              Number of equality atoms :  237 (3410 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k1_tops_1 @ X60 @ X59 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k4_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k6_subset_1 @ X39 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('28',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X58 @ X57 ) @ X57 )
      | ~ ( v4_pre_topc @ X57 @ X58 )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('42',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('55',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k6_subset_1 @ X9 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','68'])).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('71',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('73',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('74',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('87',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('90',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('92',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('94',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('98',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('100',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('103',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('104',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('105',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k6_subset_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('108',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k6_subset_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','106','111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('115',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( l1_pre_topc @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X51 @ X52 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('116',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('122',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('124',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['119','128'])).

thf('130',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
        = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('135',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','106','111','112'])).

thf('140',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','138','139'])).

thf('141',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','140'])).

thf('142',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('144',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('146',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('151',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k6_subset_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('154',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['152','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['152','155'])).

thf('158',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k6_subset_1 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['149','156','157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k6_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['144','163'])).

thf('165',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('166',plain,
    ( ( k6_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('168',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('169',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('171',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('175',plain,(
    r1_tarski @ ( k6_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('177',plain,
    ( ( k6_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('179',plain,
    ( ( k3_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('181',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('182',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('184',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('186',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k6_subset_1 @ X9 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('187',plain,
    ( ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['184','187'])).

thf('189',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('190',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k6_subset_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('196',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','194','195'])).

thf('197',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('198',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['196','201'])).

thf('203',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','194','195'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('205',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['202','205'])).

thf('207',plain,
    ( ( k6_subset_1 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['166','206'])).

thf('208',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('209',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('210',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ! [X0: $i] :
        ( ( k4_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
        = ( k2_xboole_0 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['208','211'])).

thf('213',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['207','212'])).

thf('214',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('216',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k4_subset_1 @ X42 @ X43 @ ( k3_subset_1 @ X42 @ X43 ) )
        = ( k2_subset_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('217',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('218',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k4_subset_1 @ X42 @ X43 @ ( k3_subset_1 @ X42 @ X43 ) )
        = X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['215','218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['152','155'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['214','221'])).

thf('223',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','194','195'])).

thf('224',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('225',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('226',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['224','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('232',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('234',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('236',plain,
    ( ( ( k3_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('239',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['222','223','239'])).

thf('241',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('242',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('243',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('245',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['213','240','243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('251',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['248','249','252'])).

thf('254',plain,
    ( ( ( k4_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['245','253'])).

thf('255',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['213','240','243','244'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('257',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['213','240','243','244'])).

thf('258',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['254','255','256','257'])).

thf('259',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['141','258'])).

thf('260',plain,(
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

thf('261',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v2_pre_topc @ X50 )
      | ( ( k2_pre_topc @ X50 @ X49 )
       != X49 )
      | ( v4_pre_topc @ X49 @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('262',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['259','265'])).

thf('267',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('269',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','84','85','269'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Tanhty0IU
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:56:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 19.43/19.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.43/19.64  % Solved by: fo/fo7.sh
% 19.43/19.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.43/19.64  % done 25271 iterations in 19.195s
% 19.43/19.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.43/19.64  % SZS output start Refutation
% 19.43/19.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.43/19.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.43/19.64  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 19.43/19.64  thf(sk_B_type, type, sk_B: $i).
% 19.43/19.64  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 19.43/19.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.43/19.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 19.43/19.64  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 19.43/19.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 19.43/19.64  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 19.43/19.64  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 19.43/19.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 19.43/19.64  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 19.43/19.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.43/19.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 19.43/19.64  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 19.43/19.64  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 19.43/19.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.43/19.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 19.43/19.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 19.43/19.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 19.43/19.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.43/19.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 19.43/19.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.43/19.64  thf(sk_A_type, type, sk_A: $i).
% 19.43/19.64  thf(t77_tops_1, conjecture,
% 19.43/19.64    (![A:$i]:
% 19.43/19.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 19.43/19.64       ( ![B:$i]:
% 19.43/19.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.43/19.64           ( ( v4_pre_topc @ B @ A ) <=>
% 19.43/19.64             ( ( k2_tops_1 @ A @ B ) =
% 19.43/19.64               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 19.43/19.64  thf(zf_stmt_0, negated_conjecture,
% 19.43/19.64    (~( ![A:$i]:
% 19.43/19.64        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 19.43/19.64          ( ![B:$i]:
% 19.43/19.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.43/19.64              ( ( v4_pre_topc @ B @ A ) <=>
% 19.43/19.64                ( ( k2_tops_1 @ A @ B ) =
% 19.43/19.64                  ( k7_subset_1 @
% 19.43/19.64                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 19.43/19.64    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 19.43/19.64  thf('0', plain,
% 19.43/19.64      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.64          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.64              (k1_tops_1 @ sk_A @ sk_B)))
% 19.43/19.64        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 19.43/19.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.64  thf('1', plain,
% 19.43/19.64      (~
% 19.43/19.64       (((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.64             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 19.43/19.64       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 19.43/19.64      inference('split', [status(esa)], ['0'])).
% 19.43/19.64  thf('2', plain,
% 19.43/19.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.64  thf(t74_tops_1, axiom,
% 19.43/19.64    (![A:$i]:
% 19.43/19.64     ( ( l1_pre_topc @ A ) =>
% 19.43/19.64       ( ![B:$i]:
% 19.43/19.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.43/19.64           ( ( k1_tops_1 @ A @ B ) =
% 19.43/19.64             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 19.43/19.64  thf('3', plain,
% 19.43/19.64      (![X59 : $i, X60 : $i]:
% 19.43/19.64         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 19.43/19.64          | ((k1_tops_1 @ X60 @ X59)
% 19.43/19.64              = (k7_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 19.43/19.64                 (k2_tops_1 @ X60 @ X59)))
% 19.43/19.64          | ~ (l1_pre_topc @ X60))),
% 19.43/19.64      inference('cnf', [status(esa)], [t74_tops_1])).
% 19.43/19.64  thf('4', plain,
% 19.43/19.64      ((~ (l1_pre_topc @ sk_A)
% 19.43/19.64        | ((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.64            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.64               (k2_tops_1 @ sk_A @ sk_B))))),
% 19.43/19.64      inference('sup-', [status(thm)], ['2', '3'])).
% 19.43/19.64  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 19.43/19.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.64  thf('6', plain,
% 19.43/19.64      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.64         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.64            (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['4', '5'])).
% 19.43/19.65  thf('7', plain,
% 19.43/19.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf(redefinition_k7_subset_1, axiom,
% 19.43/19.65    (![A:$i,B:$i,C:$i]:
% 19.43/19.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 19.43/19.65       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 19.43/19.65  thf('8', plain,
% 19.43/19.65      (![X39 : $i, X40 : $i, X41 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 19.43/19.65          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k4_xboole_0 @ X39 @ X41)))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 19.43/19.65  thf(redefinition_k6_subset_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 19.43/19.65  thf('9', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('10', plain,
% 19.43/19.65      (![X39 : $i, X40 : $i, X41 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 19.43/19.65          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k6_subset_1 @ X39 @ X41)))),
% 19.43/19.65      inference('demod', [status(thm)], ['8', '9'])).
% 19.43/19.65  thf('11', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 19.43/19.65           = (k6_subset_1 @ sk_B @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['7', '10'])).
% 19.43/19.65  thf('12', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['6', '11'])).
% 19.43/19.65  thf(t48_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.43/19.65  thf('13', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.43/19.65  thf('14', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('15', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('16', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('17', plain,
% 19.43/19.65      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 19.43/19.65         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['12', '16'])).
% 19.43/19.65  thf(t36_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 19.43/19.65  thf('18', plain,
% 19.43/19.65      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 19.43/19.65      inference('cnf', [status(esa)], [t36_xboole_1])).
% 19.43/19.65  thf('19', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('20', plain,
% 19.43/19.65      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 19.43/19.65      inference('demod', [status(thm)], ['18', '19'])).
% 19.43/19.65  thf(t44_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i,C:$i]:
% 19.43/19.65     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 19.43/19.65       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 19.43/19.65  thf('21', plain,
% 19.43/19.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 19.43/19.65         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 19.43/19.65          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 19.43/19.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 19.43/19.65  thf('22', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('23', plain,
% 19.43/19.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 19.43/19.65         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 19.43/19.65          | ~ (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16))),
% 19.43/19.65      inference('demod', [status(thm)], ['21', '22'])).
% 19.43/19.65  thf('24', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['20', '23'])).
% 19.43/19.65  thf('25', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65             (k1_tops_1 @ sk_A @ sk_B)))
% 19.43/19.65        | (v4_pre_topc @ sk_B @ sk_A))),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf('26', plain,
% 19.43/19.65      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('split', [status(esa)], ['25'])).
% 19.43/19.65  thf('27', plain,
% 19.43/19.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf(t69_tops_1, axiom,
% 19.43/19.65    (![A:$i]:
% 19.43/19.65     ( ( l1_pre_topc @ A ) =>
% 19.43/19.65       ( ![B:$i]:
% 19.43/19.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.43/19.65           ( ( v4_pre_topc @ B @ A ) =>
% 19.43/19.65             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 19.43/19.65  thf('28', plain,
% 19.43/19.65      (![X57 : $i, X58 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 19.43/19.65          | (r1_tarski @ (k2_tops_1 @ X58 @ X57) @ X57)
% 19.43/19.65          | ~ (v4_pre_topc @ X57 @ X58)
% 19.43/19.65          | ~ (l1_pre_topc @ X58))),
% 19.43/19.65      inference('cnf', [status(esa)], [t69_tops_1])).
% 19.43/19.65  thf('29', plain,
% 19.43/19.65      ((~ (l1_pre_topc @ sk_A)
% 19.43/19.65        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 19.43/19.65        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 19.43/19.65      inference('sup-', [status(thm)], ['27', '28'])).
% 19.43/19.65  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf('31', plain,
% 19.43/19.65      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 19.43/19.65        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 19.43/19.65      inference('demod', [status(thm)], ['29', '30'])).
% 19.43/19.65  thf('32', plain,
% 19.43/19.65      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['26', '31'])).
% 19.43/19.65  thf(t1_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i,C:$i]:
% 19.43/19.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 19.43/19.65       ( r1_tarski @ A @ C ) ))).
% 19.43/19.65  thf('33', plain,
% 19.43/19.65      (![X2 : $i, X3 : $i, X4 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X2 @ X3)
% 19.43/19.65          | ~ (r1_tarski @ X3 @ X4)
% 19.43/19.65          | (r1_tarski @ X2 @ X4))),
% 19.43/19.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 19.43/19.65  thf('34', plain,
% 19.43/19.65      ((![X0 : $i]:
% 19.43/19.65          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 19.43/19.65           | ~ (r1_tarski @ sk_B @ X0)))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['32', '33'])).
% 19.43/19.65  thf('35', plain,
% 19.43/19.65      ((![X0 : $i]:
% 19.43/19.65          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_B)))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['24', '34'])).
% 19.43/19.65  thf(commutativity_k2_tarski, axiom,
% 19.43/19.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 19.43/19.65  thf('36', plain,
% 19.43/19.65      (![X21 : $i, X22 : $i]:
% 19.43/19.65         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 19.43/19.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 19.43/19.65  thf(l51_zfmisc_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 19.43/19.65  thf('37', plain,
% 19.43/19.65      (![X23 : $i, X24 : $i]:
% 19.43/19.65         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 19.43/19.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 19.43/19.65  thf('38', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['36', '37'])).
% 19.43/19.65  thf('39', plain,
% 19.43/19.65      (![X23 : $i, X24 : $i]:
% 19.43/19.65         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 19.43/19.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 19.43/19.65  thf('40', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['38', '39'])).
% 19.43/19.65  thf(t43_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i,C:$i]:
% 19.43/19.65     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 19.43/19.65       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 19.43/19.65  thf('41', plain,
% 19.43/19.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.43/19.65         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 19.43/19.65          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 19.43/19.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 19.43/19.65  thf('42', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('43', plain,
% 19.43/19.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.43/19.65         ((r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X13)
% 19.43/19.65          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 19.43/19.65      inference('demod', [status(thm)], ['41', '42'])).
% 19.43/19.65  thf('44', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 19.43/19.65          | (r1_tarski @ (k6_subset_1 @ X2 @ X0) @ X1))),
% 19.43/19.65      inference('sup-', [status(thm)], ['40', '43'])).
% 19.43/19.65  thf('45', plain,
% 19.43/19.65      ((![X0 : $i]:
% 19.43/19.65          (r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['35', '44'])).
% 19.43/19.65  thf(t3_boole, axiom,
% 19.43/19.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 19.43/19.65  thf('46', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.43/19.65      inference('cnf', [status(esa)], [t3_boole])).
% 19.43/19.65  thf('47', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('48', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 19.43/19.65      inference('demod', [status(thm)], ['46', '47'])).
% 19.43/19.65  thf('49', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('50', plain,
% 19.43/19.65      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 19.43/19.65      inference('sup+', [status(thm)], ['48', '49'])).
% 19.43/19.65  thf(t2_boole, axiom,
% 19.43/19.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 19.43/19.65  thf('51', plain,
% 19.43/19.65      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 19.43/19.65      inference('cnf', [status(esa)], [t2_boole])).
% 19.43/19.65  thf('52', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 19.43/19.65      inference('demod', [status(thm)], ['50', '51'])).
% 19.43/19.65  thf('53', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 19.43/19.65      inference('demod', [status(thm)], ['50', '51'])).
% 19.43/19.65  thf(t38_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 19.43/19.65       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 19.43/19.65  thf('54', plain,
% 19.43/19.65      (![X8 : $i, X9 : $i]:
% 19.43/19.65         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 19.43/19.65      inference('cnf', [status(esa)], [t38_xboole_1])).
% 19.43/19.65  thf('55', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('56', plain,
% 19.43/19.65      (![X8 : $i, X9 : $i]:
% 19.43/19.65         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k6_subset_1 @ X9 @ X8)))),
% 19.43/19.65      inference('demod', [status(thm)], ['54', '55'])).
% 19.43/19.65  thf('57', plain,
% 19.43/19.65      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['53', '56'])).
% 19.43/19.65  thf('58', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X1 @ (k6_subset_1 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['52', '57'])).
% 19.43/19.65  thf('59', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 19.43/19.65      inference('demod', [status(thm)], ['50', '51'])).
% 19.43/19.65  thf('60', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('61', plain,
% 19.43/19.65      (![X0 : $i]: ((k6_subset_1 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 19.43/19.65      inference('sup+', [status(thm)], ['59', '60'])).
% 19.43/19.65  thf('62', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 19.43/19.65      inference('demod', [status(thm)], ['46', '47'])).
% 19.43/19.65  thf('63', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 19.43/19.65      inference('demod', [status(thm)], ['61', '62'])).
% 19.43/19.65  thf(t100_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 19.43/19.65  thf('64', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k4_xboole_0 @ X0 @ X1)
% 19.43/19.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 19.43/19.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.43/19.65  thf('65', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('66', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X0 @ X1)
% 19.43/19.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 19.43/19.65      inference('demod', [status(thm)], ['64', '65'])).
% 19.43/19.65  thf('67', plain,
% 19.43/19.65      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.43/19.65      inference('sup+', [status(thm)], ['63', '66'])).
% 19.43/19.65  thf('68', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 19.43/19.65      inference('demod', [status(thm)], ['58', '67'])).
% 19.43/19.65  thf('69', plain,
% 19.43/19.65      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['45', '68'])).
% 19.43/19.65  thf('70', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('71', plain,
% 19.43/19.65      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 19.43/19.65          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['69', '70'])).
% 19.43/19.65  thf('72', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 19.43/19.65      inference('demod', [status(thm)], ['46', '47'])).
% 19.43/19.65  thf('73', plain,
% 19.43/19.65      (![X21 : $i, X22 : $i]:
% 19.43/19.65         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 19.43/19.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 19.43/19.65  thf(t12_setfam_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.43/19.65  thf('74', plain,
% 19.43/19.65      (![X44 : $i, X45 : $i]:
% 19.43/19.65         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 19.43/19.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.43/19.65  thf('75', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['73', '74'])).
% 19.43/19.65  thf('76', plain,
% 19.43/19.65      (![X44 : $i, X45 : $i]:
% 19.43/19.65         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 19.43/19.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.43/19.65  thf('77', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['75', '76'])).
% 19.43/19.65  thf('78', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('demod', [status(thm)], ['71', '72', '77'])).
% 19.43/19.65  thf('79', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['17', '78'])).
% 19.43/19.65  thf('80', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 19.43/19.65           = (k6_subset_1 @ sk_B @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['7', '10'])).
% 19.43/19.65  thf('81', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65              (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= (~
% 19.43/19.65             (((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('split', [status(esa)], ['0'])).
% 19.43/19.65  thf('82', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= (~
% 19.43/19.65             (((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['80', '81'])).
% 19.43/19.65  thf('83', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 19.43/19.65         <= (~
% 19.43/19.65             (((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 19.43/19.65             ((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['79', '82'])).
% 19.43/19.65  thf('84', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 19.43/19.65       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 19.43/19.65      inference('simplify', [status(thm)], ['83'])).
% 19.43/19.65  thf('85', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 19.43/19.65       ((v4_pre_topc @ sk_B @ sk_A))),
% 19.43/19.65      inference('split', [status(esa)], ['25'])).
% 19.43/19.65  thf('86', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 19.43/19.65           = (k6_subset_1 @ sk_B @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['7', '10'])).
% 19.43/19.65  thf('87', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65             (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('split', [status(esa)], ['25'])).
% 19.43/19.65  thf('88', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['86', '87'])).
% 19.43/19.65  thf(dt_k6_subset_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 19.43/19.65  thf('89', plain,
% 19.43/19.65      (![X30 : $i, X31 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k6_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))),
% 19.43/19.65      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 19.43/19.65  thf('90', plain,
% 19.43/19.65      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['88', '89'])).
% 19.43/19.65  thf('91', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 19.43/19.65      inference('demod', [status(thm)], ['46', '47'])).
% 19.43/19.65  thf('92', plain,
% 19.43/19.65      (![X30 : $i, X31 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k6_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))),
% 19.43/19.65      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 19.43/19.65  thf('93', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 19.43/19.65      inference('sup+', [status(thm)], ['91', '92'])).
% 19.43/19.65  thf(redefinition_k4_subset_1, axiom,
% 19.43/19.65    (![A:$i,B:$i,C:$i]:
% 19.43/19.65     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 19.43/19.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 19.43/19.65       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 19.43/19.65  thf('94', plain,
% 19.43/19.65      (![X34 : $i, X35 : $i, X36 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 19.43/19.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 19.43/19.65          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 19.43/19.65  thf('95', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 19.43/19.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['93', '94'])).
% 19.43/19.65  thf('96', plain,
% 19.43/19.65      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 19.43/19.65          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['90', '95'])).
% 19.43/19.65  thf('97', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['20', '23'])).
% 19.43/19.65  thf(t3_subset, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 19.43/19.65  thf('98', plain,
% 19.43/19.65      (![X46 : $i, X48 : $i]:
% 19.43/19.65         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 19.43/19.65      inference('cnf', [status(esa)], [t3_subset])).
% 19.43/19.65  thf('99', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['97', '98'])).
% 19.43/19.65  thf(involutiveness_k3_subset_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 19.43/19.65       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 19.43/19.65  thf('100', plain,
% 19.43/19.65      (![X32 : $i, X33 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 19.43/19.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 19.43/19.65      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 19.43/19.65  thf('101', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 19.43/19.65           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['99', '100'])).
% 19.43/19.65  thf('102', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['97', '98'])).
% 19.43/19.65  thf(d5_subset_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 19.43/19.65       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 19.43/19.65  thf('103', plain,
% 19.43/19.65      (![X26 : $i, X27 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 19.43/19.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 19.43/19.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 19.43/19.65  thf('104', plain,
% 19.43/19.65      (![X37 : $i, X38 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 19.43/19.65  thf('105', plain,
% 19.43/19.65      (![X26 : $i, X27 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X26 @ X27) = (k6_subset_1 @ X26 @ X27))
% 19.43/19.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 19.43/19.65      inference('demod', [status(thm)], ['103', '104'])).
% 19.43/19.65  thf('106', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 19.43/19.65           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['102', '105'])).
% 19.43/19.65  thf('107', plain,
% 19.43/19.65      (![X30 : $i, X31 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k6_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))),
% 19.43/19.65      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 19.43/19.65  thf('108', plain,
% 19.43/19.65      (![X26 : $i, X27 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X26 @ X27) = (k6_subset_1 @ X26 @ X27))
% 19.43/19.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 19.43/19.65      inference('demod', [status(thm)], ['103', '104'])).
% 19.43/19.65  thf('109', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 19.43/19.65           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['107', '108'])).
% 19.43/19.65  thf('110', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('111', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['109', '110'])).
% 19.43/19.65  thf('112', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['75', '76'])).
% 19.43/19.65  thf('113', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 19.43/19.65      inference('demod', [status(thm)], ['101', '106', '111', '112'])).
% 19.43/19.65  thf('114', plain,
% 19.43/19.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf(dt_k2_tops_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( ( l1_pre_topc @ A ) & 
% 19.43/19.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 19.43/19.65       ( m1_subset_1 @
% 19.43/19.65         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 19.43/19.65  thf('115', plain,
% 19.43/19.65      (![X51 : $i, X52 : $i]:
% 19.43/19.65         (~ (l1_pre_topc @ X51)
% 19.43/19.65          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 19.43/19.65          | (m1_subset_1 @ (k2_tops_1 @ X51 @ X52) @ 
% 19.43/19.65             (k1_zfmisc_1 @ (u1_struct_0 @ X51))))),
% 19.43/19.65      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 19.43/19.65  thf('116', plain,
% 19.43/19.65      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.43/19.65        | ~ (l1_pre_topc @ sk_A))),
% 19.43/19.65      inference('sup-', [status(thm)], ['114', '115'])).
% 19.43/19.65  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf('118', plain,
% 19.43/19.65      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('demod', [status(thm)], ['116', '117'])).
% 19.43/19.65  thf('119', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('120', plain,
% 19.43/19.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf('121', plain,
% 19.43/19.65      (![X46 : $i, X47 : $i]:
% 19.43/19.65         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 19.43/19.65      inference('cnf', [status(esa)], [t3_subset])).
% 19.43/19.65  thf('122', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.43/19.65      inference('sup-', [status(thm)], ['120', '121'])).
% 19.43/19.65  thf('123', plain,
% 19.43/19.65      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 19.43/19.65      inference('demod', [status(thm)], ['18', '19'])).
% 19.43/19.65  thf('124', plain,
% 19.43/19.65      (![X2 : $i, X3 : $i, X4 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X2 @ X3)
% 19.43/19.65          | ~ (r1_tarski @ X3 @ X4)
% 19.43/19.65          | (r1_tarski @ X2 @ X4))),
% 19.43/19.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 19.43/19.65  thf('125', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 19.43/19.65      inference('sup-', [status(thm)], ['123', '124'])).
% 19.43/19.65  thf('126', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 19.43/19.65      inference('sup-', [status(thm)], ['122', '125'])).
% 19.43/19.65  thf('127', plain,
% 19.43/19.65      (![X46 : $i, X48 : $i]:
% 19.43/19.65         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 19.43/19.65      inference('cnf', [status(esa)], [t3_subset])).
% 19.43/19.65  thf('128', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k6_subset_1 @ sk_B @ X0) @ 
% 19.43/19.65          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['126', '127'])).
% 19.43/19.65  thf('129', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 19.43/19.65          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['119', '128'])).
% 19.43/19.65  thf('130', plain,
% 19.43/19.65      (![X34 : $i, X35 : $i, X36 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 19.43/19.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 19.43/19.65          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 19.43/19.65  thf('131', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 19.43/19.65            = (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ X1))
% 19.43/19.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['129', '130'])).
% 19.43/19.65  thf('132', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0) @ 
% 19.43/19.65           (k2_tops_1 @ sk_A @ sk_B))
% 19.43/19.65           = (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 19.43/19.65              (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['118', '131'])).
% 19.43/19.65  thf('133', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65           (k2_tops_1 @ sk_A @ sk_B))
% 19.43/19.65           = (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_B)) @ 
% 19.43/19.65              (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['113', '132'])).
% 19.43/19.65  thf('134', plain,
% 19.43/19.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf(t65_tops_1, axiom,
% 19.43/19.65    (![A:$i]:
% 19.43/19.65     ( ( l1_pre_topc @ A ) =>
% 19.43/19.65       ( ![B:$i]:
% 19.43/19.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.43/19.65           ( ( k2_pre_topc @ A @ B ) =
% 19.43/19.65             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 19.43/19.65  thf('135', plain,
% 19.43/19.65      (![X55 : $i, X56 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 19.43/19.65          | ((k2_pre_topc @ X56 @ X55)
% 19.43/19.65              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 19.43/19.65                 (k2_tops_1 @ X56 @ X55)))
% 19.43/19.65          | ~ (l1_pre_topc @ X56))),
% 19.43/19.65      inference('cnf', [status(esa)], [t65_tops_1])).
% 19.43/19.65  thf('136', plain,
% 19.43/19.65      ((~ (l1_pre_topc @ sk_A)
% 19.43/19.65        | ((k2_pre_topc @ sk_A @ sk_B)
% 19.43/19.65            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65               (k2_tops_1 @ sk_A @ sk_B))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['134', '135'])).
% 19.43/19.65  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf('138', plain,
% 19.43/19.65      (((k2_pre_topc @ sk_A @ sk_B)
% 19.43/19.65         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65            (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['136', '137'])).
% 19.43/19.65  thf('139', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 19.43/19.65      inference('demod', [status(thm)], ['101', '106', '111', '112'])).
% 19.43/19.65  thf('140', plain,
% 19.43/19.65      (((k2_pre_topc @ sk_A @ sk_B)
% 19.43/19.65         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['133', '138', '139'])).
% 19.43/19.65  thf('141', plain,
% 19.43/19.65      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 19.43/19.65          = (k2_pre_topc @ sk_A @ sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('demod', [status(thm)], ['96', '140'])).
% 19.43/19.65  thf('142', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['6', '11'])).
% 19.43/19.65  thf('143', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['109', '110'])).
% 19.43/19.65  thf('144', plain,
% 19.43/19.65      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 19.43/19.65         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['142', '143'])).
% 19.43/19.65  thf('145', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('146', plain,
% 19.43/19.65      (![X30 : $i, X31 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k6_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))),
% 19.43/19.65      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 19.43/19.65  thf('147', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['145', '146'])).
% 19.43/19.65  thf('148', plain,
% 19.43/19.65      (![X32 : $i, X33 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 19.43/19.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 19.43/19.65      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 19.43/19.65  thf('149', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup-', [status(thm)], ['147', '148'])).
% 19.43/19.65  thf('150', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['145', '146'])).
% 19.43/19.65  thf('151', plain,
% 19.43/19.65      (![X26 : $i, X27 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X26 @ X27) = (k6_subset_1 @ X26 @ X27))
% 19.43/19.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 19.43/19.65      inference('demod', [status(thm)], ['103', '104'])).
% 19.43/19.65  thf('152', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 19.43/19.65           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['150', '151'])).
% 19.43/19.65  thf('153', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('154', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('155', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.43/19.65           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['153', '154'])).
% 19.43/19.65  thf('156', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 19.43/19.65      inference('demod', [status(thm)], ['152', '155'])).
% 19.43/19.65  thf('157', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 19.43/19.65      inference('demod', [status(thm)], ['152', '155'])).
% 19.43/19.65  thf('158', plain,
% 19.43/19.65      (![X17 : $i, X18 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X17 @ (k6_subset_1 @ X17 @ X18))
% 19.43/19.65           = (k3_xboole_0 @ X17 @ X18))),
% 19.43/19.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 19.43/19.65  thf('159', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['149', '156', '157', '158'])).
% 19.43/19.65  thf('160', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X0 @ X1)
% 19.43/19.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 19.43/19.65      inference('demod', [status(thm)], ['64', '65'])).
% 19.43/19.65  thf('161', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.43/19.65           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['159', '160'])).
% 19.43/19.65  thf('162', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X0 @ X1)
% 19.43/19.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 19.43/19.65      inference('demod', [status(thm)], ['64', '65'])).
% 19.43/19.65  thf('163', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.43/19.65           = (k6_subset_1 @ X1 @ X0))),
% 19.43/19.65      inference('demod', [status(thm)], ['161', '162'])).
% 19.43/19.65  thf('164', plain,
% 19.43/19.65      (((k6_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 19.43/19.65         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['144', '163'])).
% 19.43/19.65  thf('165', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['6', '11'])).
% 19.43/19.65  thf('166', plain,
% 19.43/19.65      (((k6_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 19.43/19.65         = (k1_tops_1 @ sk_A @ sk_B))),
% 19.43/19.65      inference('demod', [status(thm)], ['164', '165'])).
% 19.43/19.65  thf('167', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['6', '11'])).
% 19.43/19.65  thf('168', plain,
% 19.43/19.65      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 19.43/19.65      inference('demod', [status(thm)], ['18', '19'])).
% 19.43/19.65  thf('169', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 19.43/19.65      inference('sup+', [status(thm)], ['167', '168'])).
% 19.43/19.65  thf('170', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 19.43/19.65      inference('demod', [status(thm)], ['46', '47'])).
% 19.43/19.65  thf('171', plain,
% 19.43/19.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 19.43/19.65         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 19.43/19.65          | ~ (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16))),
% 19.43/19.65      inference('demod', [status(thm)], ['21', '22'])).
% 19.43/19.65  thf('172', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X0 @ X1)
% 19.43/19.65          | (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['170', '171'])).
% 19.43/19.65  thf('173', plain,
% 19.43/19.65      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65        (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 19.43/19.65      inference('sup-', [status(thm)], ['169', '172'])).
% 19.43/19.65  thf('174', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 19.43/19.65          | (r1_tarski @ (k6_subset_1 @ X2 @ X0) @ X1))),
% 19.43/19.65      inference('sup-', [status(thm)], ['40', '43'])).
% 19.43/19.65  thf('175', plain,
% 19.43/19.65      ((r1_tarski @ (k6_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 19.43/19.65        k1_xboole_0)),
% 19.43/19.65      inference('sup-', [status(thm)], ['173', '174'])).
% 19.43/19.65  thf('176', plain,
% 19.43/19.65      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['53', '56'])).
% 19.43/19.65  thf('177', plain,
% 19.43/19.65      (((k6_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['175', '176'])).
% 19.43/19.65  thf('178', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['109', '110'])).
% 19.43/19.65  thf('179', plain,
% 19.43/19.65      (((k3_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 19.43/19.65         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 19.43/19.65      inference('sup+', [status(thm)], ['177', '178'])).
% 19.43/19.65  thf('180', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 19.43/19.65      inference('sup-', [status(thm)], ['122', '125'])).
% 19.43/19.65  thf('181', plain,
% 19.43/19.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 19.43/19.65         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 19.43/19.65          | ~ (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16))),
% 19.43/19.65      inference('demod', [status(thm)], ['21', '22'])).
% 19.43/19.65  thf('182', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['180', '181'])).
% 19.43/19.65  thf('183', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 19.43/19.65          | (r1_tarski @ (k6_subset_1 @ X2 @ X0) @ X1))),
% 19.43/19.65      inference('sup-', [status(thm)], ['40', '43'])).
% 19.43/19.65  thf('184', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         (r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 19.43/19.65      inference('sup-', [status(thm)], ['182', '183'])).
% 19.43/19.65  thf('185', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         (r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 19.43/19.65      inference('sup-', [status(thm)], ['182', '183'])).
% 19.43/19.65  thf('186', plain,
% 19.43/19.65      (![X8 : $i, X9 : $i]:
% 19.43/19.65         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k6_subset_1 @ X9 @ X8)))),
% 19.43/19.65      inference('demod', [status(thm)], ['54', '55'])).
% 19.43/19.65  thf('187', plain,
% 19.43/19.65      (((k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['185', '186'])).
% 19.43/19.65  thf('188', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 19.43/19.65      inference('demod', [status(thm)], ['184', '187'])).
% 19.43/19.65  thf('189', plain,
% 19.43/19.65      (![X46 : $i, X48 : $i]:
% 19.43/19.65         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 19.43/19.65      inference('cnf', [status(esa)], [t3_subset])).
% 19.43/19.65  thf('190', plain,
% 19.43/19.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['188', '189'])).
% 19.43/19.65  thf('191', plain,
% 19.43/19.65      (![X26 : $i, X27 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X26 @ X27) = (k6_subset_1 @ X26 @ X27))
% 19.43/19.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 19.43/19.65      inference('demod', [status(thm)], ['103', '104'])).
% 19.43/19.65  thf('192', plain,
% 19.43/19.65      (![X0 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['190', '191'])).
% 19.43/19.65  thf('193', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 19.43/19.65      inference('demod', [status(thm)], ['46', '47'])).
% 19.43/19.65  thf('194', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 19.43/19.65      inference('demod', [status(thm)], ['192', '193'])).
% 19.43/19.65  thf('195', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['75', '76'])).
% 19.43/19.65  thf('196', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['179', '194', '195'])).
% 19.43/19.65  thf('197', plain,
% 19.43/19.65      (![X30 : $i, X31 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k6_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))),
% 19.43/19.65      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 19.43/19.65  thf('198', plain,
% 19.43/19.65      (![X32 : $i, X33 : $i]:
% 19.43/19.65         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 19.43/19.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 19.43/19.65      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 19.43/19.65  thf('199', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 19.43/19.65           = (k6_subset_1 @ X0 @ X1))),
% 19.43/19.65      inference('sup-', [status(thm)], ['197', '198'])).
% 19.43/19.65  thf('200', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['109', '110'])).
% 19.43/19.65  thf('201', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 19.43/19.65           = (k6_subset_1 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['199', '200'])).
% 19.43/19.65  thf('202', plain,
% 19.43/19.65      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 19.43/19.65         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['196', '201'])).
% 19.43/19.65  thf('203', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['179', '194', '195'])).
% 19.43/19.65  thf('204', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k6_subset_1 @ X0 @ X1)
% 19.43/19.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 19.43/19.65      inference('demod', [status(thm)], ['64', '65'])).
% 19.43/19.65  thf('205', plain,
% 19.43/19.65      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 19.43/19.65         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['203', '204'])).
% 19.43/19.65  thf('206', plain,
% 19.43/19.65      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 19.43/19.65         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['202', '205'])).
% 19.43/19.65  thf('207', plain,
% 19.43/19.65      (((k6_subset_1 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 19.43/19.65         = (k1_tops_1 @ sk_A @ sk_B))),
% 19.43/19.65      inference('demod', [status(thm)], ['166', '206'])).
% 19.43/19.65  thf('208', plain,
% 19.43/19.65      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['88', '89'])).
% 19.43/19.65  thf('209', plain,
% 19.43/19.65      (![X30 : $i, X31 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k6_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))),
% 19.43/19.65      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 19.43/19.65  thf('210', plain,
% 19.43/19.65      (![X34 : $i, X35 : $i, X36 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 19.43/19.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 19.43/19.65          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 19.43/19.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 19.43/19.65  thf('211', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 19.43/19.65            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 19.43/19.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['209', '210'])).
% 19.43/19.65  thf('212', plain,
% 19.43/19.65      ((![X0 : $i]:
% 19.43/19.65          ((k4_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ X0) @ 
% 19.43/19.65            (k2_tops_1 @ sk_A @ sk_B))
% 19.43/19.65            = (k2_xboole_0 @ (k6_subset_1 @ sk_B @ X0) @ 
% 19.43/19.65               (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['208', '211'])).
% 19.43/19.65  thf('213', plain,
% 19.43/19.65      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65          (k2_tops_1 @ sk_A @ sk_B))
% 19.43/19.65          = (k2_xboole_0 @ 
% 19.43/19.65             (k6_subset_1 @ sk_B @ 
% 19.43/19.65              (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 19.43/19.65             (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['207', '212'])).
% 19.43/19.65  thf('214', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['86', '87'])).
% 19.43/19.65  thf('215', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['145', '146'])).
% 19.43/19.65  thf(t25_subset_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 19.43/19.65       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 19.43/19.65         ( k2_subset_1 @ A ) ) ))).
% 19.43/19.65  thf('216', plain,
% 19.43/19.65      (![X42 : $i, X43 : $i]:
% 19.43/19.65         (((k4_subset_1 @ X42 @ X43 @ (k3_subset_1 @ X42 @ X43))
% 19.43/19.65            = (k2_subset_1 @ X42))
% 19.43/19.65          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 19.43/19.65      inference('cnf', [status(esa)], [t25_subset_1])).
% 19.43/19.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 19.43/19.65  thf('217', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 19.43/19.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 19.43/19.65  thf('218', plain,
% 19.43/19.65      (![X42 : $i, X43 : $i]:
% 19.43/19.65         (((k4_subset_1 @ X42 @ X43 @ (k3_subset_1 @ X42 @ X43)) = (X42))
% 19.43/19.65          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 19.43/19.65      inference('demod', [status(thm)], ['216', '217'])).
% 19.43/19.65  thf('219', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k4_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 19.43/19.65           (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))) = (X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['215', '218'])).
% 19.43/19.65  thf('220', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 19.43/19.65      inference('demod', [status(thm)], ['152', '155'])).
% 19.43/19.65  thf('221', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k4_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 19.43/19.65           (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1))) = (X0))),
% 19.43/19.65      inference('demod', [status(thm)], ['219', '220'])).
% 19.43/19.65  thf('222', plain,
% 19.43/19.65      ((((k4_subset_1 @ sk_B @ 
% 19.43/19.65          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 19.43/19.65          (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['214', '221'])).
% 19.43/19.65  thf('223', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['179', '194', '195'])).
% 19.43/19.65  thf('224', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['86', '87'])).
% 19.43/19.65  thf('225', plain,
% 19.43/19.65      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 19.43/19.65      inference('demod', [status(thm)], ['18', '19'])).
% 19.43/19.65  thf('226', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 19.43/19.65      inference('sup-', [status(thm)], ['123', '124'])).
% 19.43/19.65  thf('227', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         (r1_tarski @ (k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X2) @ X0)),
% 19.43/19.65      inference('sup-', [status(thm)], ['225', '226'])).
% 19.43/19.65  thf('228', plain,
% 19.43/19.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 19.43/19.65         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 19.43/19.65          | ~ (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16))),
% 19.43/19.65      inference('demod', [status(thm)], ['21', '22'])).
% 19.43/19.65  thf('229', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         (r1_tarski @ (k6_subset_1 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['227', '228'])).
% 19.43/19.65  thf('230', plain,
% 19.43/19.65      ((![X0 : $i]:
% 19.43/19.65          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['224', '229'])).
% 19.43/19.65  thf('231', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 19.43/19.65          | (r1_tarski @ (k6_subset_1 @ X2 @ X0) @ X1))),
% 19.43/19.65      inference('sup-', [status(thm)], ['40', '43'])).
% 19.43/19.65  thf('232', plain,
% 19.43/19.65      ((![X0 : $i]:
% 19.43/19.65          (r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['230', '231'])).
% 19.43/19.65  thf('233', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 19.43/19.65      inference('demod', [status(thm)], ['58', '67'])).
% 19.43/19.65  thf('234', plain,
% 19.43/19.65      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['232', '233'])).
% 19.43/19.65  thf('235', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 19.43/19.65           = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['109', '110'])).
% 19.43/19.65  thf('236', plain,
% 19.43/19.65      ((((k3_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 19.43/19.65          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['234', '235'])).
% 19.43/19.65  thf('237', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 19.43/19.65      inference('demod', [status(thm)], ['192', '193'])).
% 19.43/19.65  thf('238', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['75', '76'])).
% 19.43/19.65  thf('239', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('demod', [status(thm)], ['236', '237', '238'])).
% 19.43/19.65  thf('240', plain,
% 19.43/19.65      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('demod', [status(thm)], ['222', '223', '239'])).
% 19.43/19.65  thf('241', plain,
% 19.43/19.65      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 19.43/19.65         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('sup+', [status(thm)], ['203', '204'])).
% 19.43/19.65  thf('242', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['86', '87'])).
% 19.43/19.65  thf('243', plain,
% 19.43/19.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['241', '242'])).
% 19.43/19.65  thf('244', plain,
% 19.43/19.65      (((k1_tops_1 @ sk_A @ sk_B)
% 19.43/19.65         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['6', '11'])).
% 19.43/19.65  thf('245', plain,
% 19.43/19.65      ((((sk_B)
% 19.43/19.65          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65             (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('demod', [status(thm)], ['213', '240', '243', '244'])).
% 19.43/19.65  thf('246', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['97', '98'])).
% 19.43/19.65  thf('247', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 19.43/19.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 19.43/19.65      inference('sup-', [status(thm)], ['93', '94'])).
% 19.43/19.65  thf('248', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k4_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 19.43/19.65           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 19.43/19.65      inference('sup-', [status(thm)], ['246', '247'])).
% 19.43/19.65  thf('249', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['38', '39'])).
% 19.43/19.65  thf('250', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['38', '39'])).
% 19.43/19.65  thf(t6_xboole_1, axiom,
% 19.43/19.65    (![A:$i,B:$i]:
% 19.43/19.65     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 19.43/19.65  thf('251', plain,
% 19.43/19.65      (![X19 : $i, X20 : $i]:
% 19.43/19.65         ((k2_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20))
% 19.43/19.65           = (k2_xboole_0 @ X19 @ X20))),
% 19.43/19.65      inference('cnf', [status(esa)], [t6_xboole_1])).
% 19.43/19.65  thf('252', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 19.43/19.65           = (k2_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['250', '251'])).
% 19.43/19.65  thf('253', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]:
% 19.43/19.65         ((k4_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 19.43/19.65           = (k2_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('demod', [status(thm)], ['248', '249', '252'])).
% 19.43/19.65  thf('254', plain,
% 19.43/19.65      ((((k4_subset_1 @ 
% 19.43/19.65          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 19.43/19.65          sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 19.43/19.65          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65             (k1_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['245', '253'])).
% 19.43/19.65  thf('255', plain,
% 19.43/19.65      ((((sk_B)
% 19.43/19.65          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65             (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('demod', [status(thm)], ['213', '240', '243', '244'])).
% 19.43/19.65  thf('256', plain,
% 19.43/19.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.43/19.65      inference('sup+', [status(thm)], ['38', '39'])).
% 19.43/19.65  thf('257', plain,
% 19.43/19.65      ((((sk_B)
% 19.43/19.65          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 19.43/19.65             (k2_tops_1 @ sk_A @ sk_B))))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('demod', [status(thm)], ['213', '240', '243', '244'])).
% 19.43/19.65  thf('258', plain,
% 19.43/19.65      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('demod', [status(thm)], ['254', '255', '256', '257'])).
% 19.43/19.65  thf('259', plain,
% 19.43/19.65      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup+', [status(thm)], ['141', '258'])).
% 19.43/19.65  thf('260', plain,
% 19.43/19.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf(t52_pre_topc, axiom,
% 19.43/19.65    (![A:$i]:
% 19.43/19.65     ( ( l1_pre_topc @ A ) =>
% 19.43/19.65       ( ![B:$i]:
% 19.43/19.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.43/19.65           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 19.43/19.65             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 19.43/19.65               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 19.43/19.65  thf('261', plain,
% 19.43/19.65      (![X49 : $i, X50 : $i]:
% 19.43/19.65         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 19.43/19.65          | ~ (v2_pre_topc @ X50)
% 19.43/19.65          | ((k2_pre_topc @ X50 @ X49) != (X49))
% 19.43/19.65          | (v4_pre_topc @ X49 @ X50)
% 19.43/19.65          | ~ (l1_pre_topc @ X50))),
% 19.43/19.65      inference('cnf', [status(esa)], [t52_pre_topc])).
% 19.43/19.65  thf('262', plain,
% 19.43/19.65      ((~ (l1_pre_topc @ sk_A)
% 19.43/19.65        | (v4_pre_topc @ sk_B @ sk_A)
% 19.43/19.65        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 19.43/19.65        | ~ (v2_pre_topc @ sk_A))),
% 19.43/19.65      inference('sup-', [status(thm)], ['260', '261'])).
% 19.43/19.65  thf('263', plain, ((l1_pre_topc @ sk_A)),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf('264', plain, ((v2_pre_topc @ sk_A)),
% 19.43/19.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.43/19.65  thf('265', plain,
% 19.43/19.65      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 19.43/19.65      inference('demod', [status(thm)], ['262', '263', '264'])).
% 19.43/19.65  thf('266', plain,
% 19.43/19.65      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('sup-', [status(thm)], ['259', '265'])).
% 19.43/19.65  thf('267', plain,
% 19.43/19.65      (((v4_pre_topc @ sk_B @ sk_A))
% 19.43/19.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 19.43/19.65      inference('simplify', [status(thm)], ['266'])).
% 19.43/19.65  thf('268', plain,
% 19.43/19.65      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 19.43/19.65      inference('split', [status(esa)], ['0'])).
% 19.43/19.65  thf('269', plain,
% 19.43/19.65      (~
% 19.43/19.65       (((k2_tops_1 @ sk_A @ sk_B)
% 19.43/19.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 19.43/19.65             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 19.43/19.65       ((v4_pre_topc @ sk_B @ sk_A))),
% 19.43/19.65      inference('sup-', [status(thm)], ['267', '268'])).
% 19.43/19.65  thf('270', plain, ($false),
% 19.43/19.65      inference('sat_resolution*', [status(thm)], ['1', '84', '85', '269'])).
% 19.43/19.65  
% 19.43/19.65  % SZS output end Refutation
% 19.43/19.65  
% 19.43/19.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
