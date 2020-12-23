%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qdcK9t6YZU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:42 EST 2020

% Result     : Theorem 8.69s
% Output     : Refutation 8.69s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 749 expanded)
%              Number of leaves         :   46 ( 249 expanded)
%              Depth                    :   19
%              Number of atoms          : 2073 (7480 expanded)
%              Number of equality atoms :  145 ( 445 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('11',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X56 @ X55 ) @ X55 )
      | ~ ( v4_pre_topc @ X55 @ X56 )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','26'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','26'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k1_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('51',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('53',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('55',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('56',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('61',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

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
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('84',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('92',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('95',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('100',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('104',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('111',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_pre_topc @ X54 @ X53 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 @ ( k2_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('117',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','114','115','116'])).

thf('118',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('120',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('121',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('123',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','125'])).

thf('127',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('128',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('130',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('131',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('132',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('134',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('141',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','146'])).

thf('148',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('151',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['149','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('157',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('158',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('161',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['159','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('165',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['156','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('172',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('173',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('175',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['155','170','179'])).

thf('181',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','180'])).

thf('182',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['117','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('184',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X49 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('185',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['182','188'])).

thf('190',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('191',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','68','69','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qdcK9t6YZU
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 8.69/8.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.69/8.89  % Solved by: fo/fo7.sh
% 8.69/8.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.69/8.89  % done 16952 iterations in 8.438s
% 8.69/8.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.69/8.89  % SZS output start Refutation
% 8.69/8.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.69/8.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.69/8.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.69/8.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.69/8.89  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.69/8.89  thf(sk_A_type, type, sk_A: $i).
% 8.69/8.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.69/8.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 8.69/8.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 8.69/8.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.69/8.89  thf(sk_B_type, type, sk_B: $i).
% 8.69/8.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.69/8.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 8.69/8.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.69/8.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.69/8.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.69/8.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.69/8.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.69/8.89  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 8.69/8.89  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.69/8.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.69/8.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.69/8.89  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.69/8.89  thf(t77_tops_1, conjecture,
% 8.69/8.89    (![A:$i]:
% 8.69/8.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.69/8.89       ( ![B:$i]:
% 8.69/8.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.69/8.89           ( ( v4_pre_topc @ B @ A ) <=>
% 8.69/8.89             ( ( k2_tops_1 @ A @ B ) =
% 8.69/8.89               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 8.69/8.89  thf(zf_stmt_0, negated_conjecture,
% 8.69/8.89    (~( ![A:$i]:
% 8.69/8.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.69/8.89          ( ![B:$i]:
% 8.69/8.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.69/8.89              ( ( v4_pre_topc @ B @ A ) <=>
% 8.69/8.89                ( ( k2_tops_1 @ A @ B ) =
% 8.69/8.89                  ( k7_subset_1 @
% 8.69/8.89                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 8.69/8.89    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 8.69/8.89  thf('0', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89              (k1_tops_1 @ sk_A @ sk_B)))
% 8.69/8.89        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('1', plain,
% 8.69/8.89      (~
% 8.69/8.89       (((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 8.69/8.89       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 8.69/8.89      inference('split', [status(esa)], ['0'])).
% 8.69/8.89  thf(commutativity_k2_tarski, axiom,
% 8.69/8.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 8.69/8.89  thf('2', plain,
% 8.69/8.89      (![X23 : $i, X24 : $i]:
% 8.69/8.89         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 8.69/8.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.69/8.89  thf(t12_setfam_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.69/8.89  thf('3', plain,
% 8.69/8.89      (![X42 : $i, X43 : $i]:
% 8.69/8.89         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 8.69/8.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.69/8.89  thf('4', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['2', '3'])).
% 8.69/8.89  thf('5', plain,
% 8.69/8.89      (![X42 : $i, X43 : $i]:
% 8.69/8.89         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 8.69/8.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.69/8.89  thf('6', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['4', '5'])).
% 8.69/8.89  thf(t7_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 8.69/8.89  thf('7', plain,
% 8.69/8.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 8.69/8.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.69/8.89  thf('8', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89             (k1_tops_1 @ sk_A @ sk_B)))
% 8.69/8.89        | (v4_pre_topc @ sk_B @ sk_A))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('9', plain,
% 8.69/8.89      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('split', [status(esa)], ['8'])).
% 8.69/8.89  thf('10', plain,
% 8.69/8.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf(t69_tops_1, axiom,
% 8.69/8.89    (![A:$i]:
% 8.69/8.89     ( ( l1_pre_topc @ A ) =>
% 8.69/8.89       ( ![B:$i]:
% 8.69/8.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.69/8.89           ( ( v4_pre_topc @ B @ A ) =>
% 8.69/8.89             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 8.69/8.89  thf('11', plain,
% 8.69/8.89      (![X55 : $i, X56 : $i]:
% 8.69/8.89         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 8.69/8.89          | (r1_tarski @ (k2_tops_1 @ X56 @ X55) @ X55)
% 8.69/8.89          | ~ (v4_pre_topc @ X55 @ X56)
% 8.69/8.89          | ~ (l1_pre_topc @ X56))),
% 8.69/8.89      inference('cnf', [status(esa)], [t69_tops_1])).
% 8.69/8.89  thf('12', plain,
% 8.69/8.89      ((~ (l1_pre_topc @ sk_A)
% 8.69/8.89        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 8.69/8.89        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 8.69/8.89      inference('sup-', [status(thm)], ['10', '11'])).
% 8.69/8.89  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('14', plain,
% 8.69/8.89      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 8.69/8.89        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 8.69/8.89      inference('demod', [status(thm)], ['12', '13'])).
% 8.69/8.89  thf('15', plain,
% 8.69/8.89      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['9', '14'])).
% 8.69/8.89  thf(t1_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i,C:$i]:
% 8.69/8.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.69/8.89       ( r1_tarski @ A @ C ) ))).
% 8.69/8.89  thf('16', plain,
% 8.69/8.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.69/8.89         (~ (r1_tarski @ X2 @ X3)
% 8.69/8.89          | ~ (r1_tarski @ X3 @ X4)
% 8.69/8.89          | (r1_tarski @ X2 @ X4))),
% 8.69/8.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.69/8.89  thf('17', plain,
% 8.69/8.89      ((![X0 : $i]:
% 8.69/8.89          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 8.69/8.89           | ~ (r1_tarski @ sk_B @ X0)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['15', '16'])).
% 8.69/8.89  thf('18', plain,
% 8.69/8.89      ((![X0 : $i]:
% 8.69/8.89          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['7', '17'])).
% 8.69/8.89  thf(t43_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i,C:$i]:
% 8.69/8.89     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 8.69/8.89       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 8.69/8.89  thf('19', plain,
% 8.69/8.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.69/8.89         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 8.69/8.89          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.69/8.89  thf('20', plain,
% 8.69/8.89      ((![X0 : $i]:
% 8.69/8.89          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['18', '19'])).
% 8.69/8.89  thf(t38_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 8.69/8.89       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 8.69/8.89  thf('21', plain,
% 8.69/8.89      (![X8 : $i, X9 : $i]:
% 8.69/8.89         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t38_xboole_1])).
% 8.69/8.89  thf('22', plain,
% 8.69/8.89      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['20', '21'])).
% 8.69/8.89  thf(t48_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.69/8.89  thf('23', plain,
% 8.69/8.89      (![X19 : $i, X20 : $i]:
% 8.69/8.89         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 8.69/8.89           = (k3_xboole_0 @ X19 @ X20))),
% 8.69/8.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.69/8.89  thf('24', plain,
% 8.69/8.89      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 8.69/8.89          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['22', '23'])).
% 8.69/8.89  thf(t3_boole, axiom,
% 8.69/8.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.69/8.89  thf('25', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_boole])).
% 8.69/8.89  thf('26', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('demod', [status(thm)], ['24', '25'])).
% 8.69/8.89  thf('27', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['6', '26'])).
% 8.69/8.89  thf(t100_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.69/8.89  thf('28', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k4_xboole_0 @ X0 @ X1)
% 8.69/8.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.69/8.89  thf(t36_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.69/8.89  thf('29', plain,
% 8.69/8.89      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 8.69/8.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.69/8.89  thf(t3_subset, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.69/8.89  thf('30', plain,
% 8.69/8.89      (![X44 : $i, X46 : $i]:
% 8.69/8.89         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.69/8.89  thf('31', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['29', '30'])).
% 8.69/8.89  thf('32', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         (m1_subset_1 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.69/8.89          (k1_zfmisc_1 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['28', '31'])).
% 8.69/8.89  thf(d5_subset_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.69/8.89       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.69/8.89  thf('33', plain,
% 8.69/8.89      (![X28 : $i, X29 : $i]:
% 8.69/8.89         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.69/8.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.69/8.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.69/8.89  thf('34', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k3_subset_1 @ X0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 8.69/8.89           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['32', '33'])).
% 8.69/8.89  thf('35', plain,
% 8.69/8.89      ((((k3_subset_1 @ sk_B @ 
% 8.69/8.89          (k5_xboole_0 @ sk_B @ 
% 8.69/8.89           (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89          = (k4_xboole_0 @ sk_B @ 
% 8.69/8.89             (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['27', '34'])).
% 8.69/8.89  thf('36', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['6', '26'])).
% 8.69/8.89  thf('37', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['6', '26'])).
% 8.69/8.89  thf('38', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k4_xboole_0 @ X0 @ X1)
% 8.69/8.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.69/8.89  thf('39', plain,
% 8.69/8.89      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.69/8.89          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['37', '38'])).
% 8.69/8.89  thf('40', plain,
% 8.69/8.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf(t74_tops_1, axiom,
% 8.69/8.89    (![A:$i]:
% 8.69/8.89     ( ( l1_pre_topc @ A ) =>
% 8.69/8.89       ( ![B:$i]:
% 8.69/8.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.69/8.89           ( ( k1_tops_1 @ A @ B ) =
% 8.69/8.89             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.69/8.89  thf('41', plain,
% 8.69/8.89      (![X57 : $i, X58 : $i]:
% 8.69/8.89         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 8.69/8.89          | ((k1_tops_1 @ X58 @ X57)
% 8.69/8.89              = (k7_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 8.69/8.89                 (k2_tops_1 @ X58 @ X57)))
% 8.69/8.89          | ~ (l1_pre_topc @ X58))),
% 8.69/8.89      inference('cnf', [status(esa)], [t74_tops_1])).
% 8.69/8.89  thf('42', plain,
% 8.69/8.89      ((~ (l1_pre_topc @ sk_A)
% 8.69/8.89        | ((k1_tops_1 @ sk_A @ sk_B)
% 8.69/8.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['40', '41'])).
% 8.69/8.89  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('44', plain,
% 8.69/8.89      (((k1_tops_1 @ sk_A @ sk_B)
% 8.69/8.89         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.69/8.89      inference('demod', [status(thm)], ['42', '43'])).
% 8.69/8.89  thf('45', plain,
% 8.69/8.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf(redefinition_k7_subset_1, axiom,
% 8.69/8.89    (![A:$i,B:$i,C:$i]:
% 8.69/8.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.69/8.89       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.69/8.89  thf('46', plain,
% 8.69/8.89      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.69/8.89         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.69/8.89          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 8.69/8.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.69/8.89  thf('47', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.69/8.89           = (k4_xboole_0 @ sk_B @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['45', '46'])).
% 8.69/8.89  thf('48', plain,
% 8.69/8.89      (((k1_tops_1 @ sk_A @ sk_B)
% 8.69/8.89         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.69/8.89      inference('demod', [status(thm)], ['44', '47'])).
% 8.69/8.89  thf('49', plain,
% 8.69/8.89      ((((k1_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['39', '48'])).
% 8.69/8.89  thf('50', plain,
% 8.69/8.89      ((((k1_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['39', '48'])).
% 8.69/8.89  thf('51', plain,
% 8.69/8.89      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.69/8.89          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('demod', [status(thm)], ['35', '36', '49', '50'])).
% 8.69/8.89  thf('52', plain,
% 8.69/8.89      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['9', '14'])).
% 8.69/8.89  thf('53', plain,
% 8.69/8.89      (![X44 : $i, X46 : $i]:
% 8.69/8.89         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.69/8.89  thf('54', plain,
% 8.69/8.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['52', '53'])).
% 8.69/8.89  thf(involutiveness_k3_subset_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.69/8.89       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 8.69/8.89  thf('55', plain,
% 8.69/8.89      (![X32 : $i, X33 : $i]:
% 8.69/8.89         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 8.69/8.89          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 8.69/8.89      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.69/8.89  thf('56', plain,
% 8.69/8.89      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 8.69/8.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['54', '55'])).
% 8.69/8.89  thf('57', plain,
% 8.69/8.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['52', '53'])).
% 8.69/8.89  thf('58', plain,
% 8.69/8.89      (![X28 : $i, X29 : $i]:
% 8.69/8.89         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.69/8.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.69/8.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.69/8.89  thf('59', plain,
% 8.69/8.89      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.69/8.89          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['57', '58'])).
% 8.69/8.89  thf('60', plain,
% 8.69/8.89      (((k1_tops_1 @ sk_A @ sk_B)
% 8.69/8.89         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.69/8.89      inference('demod', [status(thm)], ['44', '47'])).
% 8.69/8.89  thf('61', plain,
% 8.69/8.89      ((((k1_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['59', '60'])).
% 8.69/8.89  thf('62', plain,
% 8.69/8.89      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.69/8.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('demod', [status(thm)], ['56', '61'])).
% 8.69/8.89  thf('63', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('demod', [status(thm)], ['51', '62'])).
% 8.69/8.89  thf('64', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.69/8.89           = (k4_xboole_0 @ sk_B @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['45', '46'])).
% 8.69/8.89  thf('65', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89              (k1_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (~
% 8.69/8.89             (((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('split', [status(esa)], ['0'])).
% 8.69/8.89  thf('66', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= (~
% 8.69/8.89             (((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['64', '65'])).
% 8.69/8.89  thf('67', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 8.69/8.89         <= (~
% 8.69/8.89             (((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 8.69/8.89             ((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['63', '66'])).
% 8.69/8.89  thf('68', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 8.69/8.89       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 8.69/8.89      inference('simplify', [status(thm)], ['67'])).
% 8.69/8.89  thf('69', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 8.69/8.89       ((v4_pre_topc @ sk_B @ sk_A))),
% 8.69/8.89      inference('split', [status(esa)], ['8'])).
% 8.69/8.89  thf('70', plain,
% 8.69/8.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 8.69/8.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.69/8.89  thf('71', plain,
% 8.69/8.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('72', plain,
% 8.69/8.89      (![X44 : $i, X45 : $i]:
% 8.69/8.89         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.69/8.89  thf('73', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.69/8.89      inference('sup-', [status(thm)], ['71', '72'])).
% 8.69/8.89  thf('74', plain,
% 8.69/8.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.69/8.89         (~ (r1_tarski @ X2 @ X3)
% 8.69/8.89          | ~ (r1_tarski @ X3 @ X4)
% 8.69/8.89          | (r1_tarski @ X2 @ X4))),
% 8.69/8.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.69/8.89  thf('75', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['73', '74'])).
% 8.69/8.89  thf('76', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['70', '75'])).
% 8.69/8.89  thf('77', plain,
% 8.69/8.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.69/8.89         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 8.69/8.89          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.69/8.89  thf('78', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 8.69/8.89      inference('sup-', [status(thm)], ['76', '77'])).
% 8.69/8.89  thf('79', plain,
% 8.69/8.89      (![X8 : $i, X9 : $i]:
% 8.69/8.89         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t38_xboole_1])).
% 8.69/8.89  thf('80', plain,
% 8.69/8.89      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['78', '79'])).
% 8.69/8.89  thf('81', plain,
% 8.69/8.89      (![X19 : $i, X20 : $i]:
% 8.69/8.89         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 8.69/8.89           = (k3_xboole_0 @ X19 @ X20))),
% 8.69/8.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.69/8.89  thf('82', plain,
% 8.69/8.89      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 8.69/8.89         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['80', '81'])).
% 8.69/8.89  thf('83', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_boole])).
% 8.69/8.89  thf('84', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('demod', [status(thm)], ['82', '83'])).
% 8.69/8.89  thf('85', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['4', '5'])).
% 8.69/8.89  thf('86', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k4_xboole_0 @ X0 @ X1)
% 8.69/8.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.69/8.89  thf('87', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k4_xboole_0 @ X0 @ X1)
% 8.69/8.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.69/8.89      inference('sup+', [status(thm)], ['85', '86'])).
% 8.69/8.89  thf('88', plain,
% 8.69/8.89      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 8.69/8.89         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 8.69/8.89      inference('sup+', [status(thm)], ['84', '87'])).
% 8.69/8.89  thf('89', plain,
% 8.69/8.89      (![X19 : $i, X20 : $i]:
% 8.69/8.89         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 8.69/8.89           = (k3_xboole_0 @ X19 @ X20))),
% 8.69/8.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.69/8.89  thf('90', plain,
% 8.69/8.89      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 8.69/8.89         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 8.69/8.89         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 8.69/8.89      inference('sup+', [status(thm)], ['88', '89'])).
% 8.69/8.89  thf('91', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['4', '5'])).
% 8.69/8.89  thf('92', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('demod', [status(thm)], ['82', '83'])).
% 8.69/8.89  thf('93', plain,
% 8.69/8.89      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 8.69/8.89         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 8.69/8.89      inference('demod', [status(thm)], ['90', '91', '92'])).
% 8.69/8.89  thf('94', plain,
% 8.69/8.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf(dt_k2_tops_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( ( l1_pre_topc @ A ) & 
% 8.69/8.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.69/8.89       ( m1_subset_1 @
% 8.69/8.89         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.69/8.89  thf('95', plain,
% 8.69/8.89      (![X47 : $i, X48 : $i]:
% 8.69/8.89         (~ (l1_pre_topc @ X47)
% 8.69/8.89          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 8.69/8.89          | (m1_subset_1 @ (k2_tops_1 @ X47 @ X48) @ 
% 8.69/8.89             (k1_zfmisc_1 @ (u1_struct_0 @ X47))))),
% 8.69/8.89      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 8.69/8.89  thf('96', plain,
% 8.69/8.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.69/8.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.69/8.89        | ~ (l1_pre_topc @ sk_A))),
% 8.69/8.89      inference('sup-', [status(thm)], ['94', '95'])).
% 8.69/8.89  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('98', plain,
% 8.69/8.89      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.69/8.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('demod', [status(thm)], ['96', '97'])).
% 8.69/8.89  thf('99', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['29', '30'])).
% 8.69/8.89  thf(redefinition_k4_subset_1, axiom,
% 8.69/8.89    (![A:$i,B:$i,C:$i]:
% 8.69/8.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.69/8.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.69/8.89       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 8.69/8.89  thf('100', plain,
% 8.69/8.89      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.69/8.89         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 8.69/8.89          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 8.69/8.89          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 8.69/8.89      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.69/8.89  thf('101', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.69/8.89         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 8.69/8.89            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 8.69/8.89          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['99', '100'])).
% 8.69/8.89  thf('102', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.69/8.89           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 8.69/8.89           (k2_tops_1 @ sk_A @ sk_B))
% 8.69/8.89           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 8.69/8.89              (k2_tops_1 @ sk_A @ sk_B)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['98', '101'])).
% 8.69/8.89  thf('103', plain,
% 8.69/8.89      (![X23 : $i, X24 : $i]:
% 8.69/8.89         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 8.69/8.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.69/8.89  thf(l51_zfmisc_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.69/8.89  thf('104', plain,
% 8.69/8.89      (![X25 : $i, X26 : $i]:
% 8.69/8.89         ((k3_tarski @ (k2_tarski @ X25 @ X26)) = (k2_xboole_0 @ X25 @ X26))),
% 8.69/8.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.69/8.89  thf('105', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['103', '104'])).
% 8.69/8.89  thf('106', plain,
% 8.69/8.89      (![X25 : $i, X26 : $i]:
% 8.69/8.89         ((k3_tarski @ (k2_tarski @ X25 @ X26)) = (k2_xboole_0 @ X25 @ X26))),
% 8.69/8.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.69/8.89  thf('107', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['105', '106'])).
% 8.69/8.89  thf('108', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.69/8.89           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 8.69/8.89           (k2_tops_1 @ sk_A @ sk_B))
% 8.69/8.89           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.69/8.89              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 8.69/8.89      inference('demod', [status(thm)], ['102', '107'])).
% 8.69/8.89  thf('109', plain,
% 8.69/8.89      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.69/8.89         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.69/8.89            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 8.69/8.89             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 8.69/8.89      inference('sup+', [status(thm)], ['93', '108'])).
% 8.69/8.89  thf('110', plain,
% 8.69/8.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf(t65_tops_1, axiom,
% 8.69/8.89    (![A:$i]:
% 8.69/8.89     ( ( l1_pre_topc @ A ) =>
% 8.69/8.89       ( ![B:$i]:
% 8.69/8.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.69/8.89           ( ( k2_pre_topc @ A @ B ) =
% 8.69/8.89             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.69/8.89  thf('111', plain,
% 8.69/8.89      (![X53 : $i, X54 : $i]:
% 8.69/8.89         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 8.69/8.89          | ((k2_pre_topc @ X54 @ X53)
% 8.69/8.89              = (k4_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 8.69/8.89                 (k2_tops_1 @ X54 @ X53)))
% 8.69/8.89          | ~ (l1_pre_topc @ X54))),
% 8.69/8.89      inference('cnf', [status(esa)], [t65_tops_1])).
% 8.69/8.89  thf('112', plain,
% 8.69/8.89      ((~ (l1_pre_topc @ sk_A)
% 8.69/8.89        | ((k2_pre_topc @ sk_A @ sk_B)
% 8.69/8.89            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['110', '111'])).
% 8.69/8.89  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('114', plain,
% 8.69/8.89      (((k2_pre_topc @ sk_A @ sk_B)
% 8.69/8.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.69/8.89      inference('demod', [status(thm)], ['112', '113'])).
% 8.69/8.89  thf('115', plain,
% 8.69/8.89      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 8.69/8.89         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 8.69/8.89      inference('demod', [status(thm)], ['90', '91', '92'])).
% 8.69/8.89  thf('116', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.69/8.89      inference('sup+', [status(thm)], ['105', '106'])).
% 8.69/8.89  thf('117', plain,
% 8.69/8.89      (((k2_pre_topc @ sk_A @ sk_B)
% 8.69/8.89         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.69/8.89      inference('demod', [status(thm)], ['109', '114', '115', '116'])).
% 8.69/8.89  thf('118', plain,
% 8.69/8.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 8.69/8.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.69/8.89  thf('119', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.69/8.89           = (k4_xboole_0 @ sk_B @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['45', '46'])).
% 8.69/8.89  thf('120', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89             (k1_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('split', [status(esa)], ['8'])).
% 8.69/8.89  thf('121', plain,
% 8.69/8.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup+', [status(thm)], ['119', '120'])).
% 8.69/8.89  thf('122', plain,
% 8.69/8.89      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 8.69/8.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.69/8.89  thf('123', plain,
% 8.69/8.89      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup+', [status(thm)], ['121', '122'])).
% 8.69/8.89  thf('124', plain,
% 8.69/8.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.69/8.89         (~ (r1_tarski @ X2 @ X3)
% 8.69/8.89          | ~ (r1_tarski @ X3 @ X4)
% 8.69/8.89          | (r1_tarski @ X2 @ X4))),
% 8.69/8.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.69/8.89  thf('125', plain,
% 8.69/8.89      ((![X0 : $i]:
% 8.69/8.89          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 8.69/8.89           | ~ (r1_tarski @ sk_B @ X0)))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['123', '124'])).
% 8.69/8.89  thf('126', plain,
% 8.69/8.89      ((![X0 : $i]:
% 8.69/8.89          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['118', '125'])).
% 8.69/8.89  thf('127', plain,
% 8.69/8.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.69/8.89         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 8.69/8.89          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.69/8.89  thf('128', plain,
% 8.69/8.89      ((![X0 : $i]:
% 8.69/8.89          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['126', '127'])).
% 8.69/8.89  thf('129', plain,
% 8.69/8.89      (![X8 : $i, X9 : $i]:
% 8.69/8.89         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t38_xboole_1])).
% 8.69/8.89  thf('130', plain,
% 8.69/8.89      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup-', [status(thm)], ['128', '129'])).
% 8.69/8.89  thf(t39_xboole_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.69/8.89  thf('131', plain,
% 8.69/8.89      (![X10 : $i, X11 : $i]:
% 8.69/8.89         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 8.69/8.89           = (k2_xboole_0 @ X10 @ X11))),
% 8.69/8.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.69/8.89  thf('132', plain,
% 8.69/8.89      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 8.69/8.89          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup+', [status(thm)], ['130', '131'])).
% 8.69/8.89  thf('133', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_boole])).
% 8.69/8.89  thf('134', plain,
% 8.69/8.89      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 8.69/8.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.69/8.89  thf('135', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.69/8.89      inference('sup+', [status(thm)], ['133', '134'])).
% 8.69/8.89  thf('136', plain,
% 8.69/8.89      (![X44 : $i, X46 : $i]:
% 8.69/8.89         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.69/8.89  thf('137', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['135', '136'])).
% 8.69/8.89  thf('138', plain,
% 8.69/8.89      (![X28 : $i, X29 : $i]:
% 8.69/8.89         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.69/8.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.69/8.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.69/8.89  thf('139', plain,
% 8.69/8.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['137', '138'])).
% 8.69/8.89  thf('140', plain,
% 8.69/8.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 8.69/8.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.69/8.89  thf('141', plain,
% 8.69/8.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.69/8.89         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 8.69/8.89          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.69/8.89  thf('142', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 8.69/8.89      inference('sup-', [status(thm)], ['140', '141'])).
% 8.69/8.89  thf('143', plain,
% 8.69/8.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['137', '138'])).
% 8.69/8.89  thf('144', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_subset_1 @ X1 @ X1) @ X0)),
% 8.69/8.89      inference('demod', [status(thm)], ['142', '143'])).
% 8.69/8.89  thf('145', plain,
% 8.69/8.89      (![X8 : $i, X9 : $i]:
% 8.69/8.89         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t38_xboole_1])).
% 8.69/8.89  thf('146', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['144', '145'])).
% 8.69/8.89  thf('147', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 8.69/8.89      inference('demod', [status(thm)], ['139', '146'])).
% 8.69/8.89  thf('148', plain,
% 8.69/8.89      (![X10 : $i, X11 : $i]:
% 8.69/8.89         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 8.69/8.89           = (k2_xboole_0 @ X10 @ X11))),
% 8.69/8.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.69/8.89  thf('149', plain,
% 8.69/8.89      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 8.69/8.89      inference('sup+', [status(thm)], ['147', '148'])).
% 8.69/8.89  thf('150', plain,
% 8.69/8.89      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 8.69/8.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.69/8.89  thf('151', plain,
% 8.69/8.89      (![X44 : $i, X46 : $i]:
% 8.69/8.89         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.69/8.89  thf('152', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['150', '151'])).
% 8.69/8.89  thf('153', plain,
% 8.69/8.89      (![X32 : $i, X33 : $i]:
% 8.69/8.89         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 8.69/8.89          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 8.69/8.89      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.69/8.89  thf('154', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 8.69/8.89           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 8.69/8.89      inference('sup-', [status(thm)], ['152', '153'])).
% 8.69/8.89  thf('155', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 8.69/8.89           (k3_subset_1 @ (k2_xboole_0 @ X0 @ X0) @ X0)) = (X0))),
% 8.69/8.89      inference('sup+', [status(thm)], ['149', '154'])).
% 8.69/8.89  thf('156', plain,
% 8.69/8.89      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 8.69/8.89      inference('sup+', [status(thm)], ['147', '148'])).
% 8.69/8.89  thf('157', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.69/8.89      inference('sup+', [status(thm)], ['133', '134'])).
% 8.69/8.89  thf('158', plain,
% 8.69/8.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.69/8.89         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 8.69/8.89          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.69/8.89  thf('159', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 8.69/8.89      inference('sup-', [status(thm)], ['157', '158'])).
% 8.69/8.89  thf('160', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['150', '151'])).
% 8.69/8.89  thf('161', plain,
% 8.69/8.89      (![X28 : $i, X29 : $i]:
% 8.69/8.89         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.69/8.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.69/8.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.69/8.89  thf('162', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 8.69/8.89           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 8.69/8.89      inference('sup-', [status(thm)], ['160', '161'])).
% 8.69/8.89  thf('163', plain,
% 8.69/8.89      (![X0 : $i, X1 : $i]:
% 8.69/8.89         (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 8.69/8.89      inference('demod', [status(thm)], ['159', '162'])).
% 8.69/8.89  thf('164', plain,
% 8.69/8.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['137', '138'])).
% 8.69/8.89  thf('165', plain,
% 8.69/8.89      (![X8 : $i, X9 : $i]:
% 8.69/8.89         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 8.69/8.89      inference('cnf', [status(esa)], [t38_xboole_1])).
% 8.69/8.89  thf('166', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X0)) | ((X0) = (k1_xboole_0)))),
% 8.69/8.89      inference('sup-', [status(thm)], ['164', '165'])).
% 8.69/8.89  thf('167', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['144', '145'])).
% 8.69/8.89  thf('168', plain,
% 8.69/8.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.69/8.89      inference('demod', [status(thm)], ['166', '167'])).
% 8.69/8.89  thf('169', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['163', '168'])).
% 8.69/8.89  thf('170', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X0) @ X0) = (k1_xboole_0))),
% 8.69/8.89      inference('sup+', [status(thm)], ['156', '169'])).
% 8.69/8.89  thf('171', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 8.69/8.89      inference('sup-', [status(thm)], ['76', '77'])).
% 8.69/8.89  thf('172', plain,
% 8.69/8.89      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['78', '79'])).
% 8.69/8.89  thf('173', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.69/8.89      inference('demod', [status(thm)], ['171', '172'])).
% 8.69/8.89  thf('174', plain,
% 8.69/8.89      (![X44 : $i, X46 : $i]:
% 8.69/8.89         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.69/8.89  thf('175', plain,
% 8.69/8.89      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['173', '174'])).
% 8.69/8.89  thf('176', plain,
% 8.69/8.89      (![X28 : $i, X29 : $i]:
% 8.69/8.89         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.69/8.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.69/8.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.69/8.89  thf('177', plain,
% 8.69/8.89      (![X0 : $i]:
% 8.69/8.89         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 8.69/8.89      inference('sup-', [status(thm)], ['175', '176'])).
% 8.69/8.89  thf('178', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 8.69/8.89      inference('cnf', [status(esa)], [t3_boole])).
% 8.69/8.89  thf('179', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.69/8.89      inference('sup+', [status(thm)], ['177', '178'])).
% 8.69/8.89  thf('180', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.69/8.89      inference('demod', [status(thm)], ['155', '170', '179'])).
% 8.69/8.89  thf('181', plain,
% 8.69/8.89      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('demod', [status(thm)], ['132', '180'])).
% 8.69/8.89  thf('182', plain,
% 8.69/8.89      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup+', [status(thm)], ['117', '181'])).
% 8.69/8.89  thf('183', plain,
% 8.69/8.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf(fc1_tops_1, axiom,
% 8.69/8.89    (![A:$i,B:$i]:
% 8.69/8.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 8.69/8.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.69/8.89       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 8.69/8.89  thf('184', plain,
% 8.69/8.89      (![X49 : $i, X50 : $i]:
% 8.69/8.89         (~ (l1_pre_topc @ X49)
% 8.69/8.89          | ~ (v2_pre_topc @ X49)
% 8.69/8.89          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 8.69/8.89          | (v4_pre_topc @ (k2_pre_topc @ X49 @ X50) @ X49))),
% 8.69/8.89      inference('cnf', [status(esa)], [fc1_tops_1])).
% 8.69/8.89  thf('185', plain,
% 8.69/8.89      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 8.69/8.89        | ~ (v2_pre_topc @ sk_A)
% 8.69/8.89        | ~ (l1_pre_topc @ sk_A))),
% 8.69/8.89      inference('sup-', [status(thm)], ['183', '184'])).
% 8.69/8.89  thf('186', plain, ((v2_pre_topc @ sk_A)),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 8.69/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.69/8.89  thf('188', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 8.69/8.89      inference('demod', [status(thm)], ['185', '186', '187'])).
% 8.69/8.89  thf('189', plain,
% 8.69/8.89      (((v4_pre_topc @ sk_B @ sk_A))
% 8.69/8.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.69/8.89      inference('sup+', [status(thm)], ['182', '188'])).
% 8.69/8.89  thf('190', plain,
% 8.69/8.89      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 8.69/8.89      inference('split', [status(esa)], ['0'])).
% 8.69/8.89  thf('191', plain,
% 8.69/8.89      (~
% 8.69/8.89       (((k2_tops_1 @ sk_A @ sk_B)
% 8.69/8.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.69/8.89             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 8.69/8.89       ((v4_pre_topc @ sk_B @ sk_A))),
% 8.69/8.89      inference('sup-', [status(thm)], ['189', '190'])).
% 8.69/8.89  thf('192', plain, ($false),
% 8.69/8.89      inference('sat_resolution*', [status(thm)], ['1', '68', '69', '191'])).
% 8.69/8.89  
% 8.69/8.89  % SZS output end Refutation
% 8.69/8.89  
% 8.69/8.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
