%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R5dhbRo76D

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:58 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 487 expanded)
%              Number of leaves         :   37 ( 160 expanded)
%              Depth                    :   20
%              Number of atoms          : 1284 (5149 expanded)
%              Number of equality atoms :  107 ( 404 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_tops_1 @ X39 @ X38 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ X38 ) @ ( k1_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

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
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_pre_topc @ X43 @ X42 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X43 ) @ X42 @ ( k2_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X45 @ X44 ) @ X44 )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','61'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('64',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('66',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['19','66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('72',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('77',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('79',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','60'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('87',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('89',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('92',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X36 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('93',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','96'])).

thf('98',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('99',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('101',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['69','99','100'])).

thf('102',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['67','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('104',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','102','103'])).

thf('105',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['68'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('107',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['69','99'])).

thf('109',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R5dhbRo76D
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:49 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 1721 iterations in 0.433s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.68/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.68/0.89  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.68/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.89  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.68/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.89  thf(t77_tops_1, conjecture,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( v4_pre_topc @ B @ A ) <=>
% 0.68/0.89             ( ( k2_tops_1 @ A @ B ) =
% 0.68/0.89               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i]:
% 0.68/0.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.89          ( ![B:$i]:
% 0.68/0.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89              ( ( v4_pre_topc @ B @ A ) <=>
% 0.68/0.89                ( ( k2_tops_1 @ A @ B ) =
% 0.68/0.89                  ( k7_subset_1 @
% 0.68/0.89                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(l78_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( k2_tops_1 @ A @ B ) =
% 0.68/0.89             ( k7_subset_1 @
% 0.68/0.89               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.68/0.89               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      (![X38 : $i, X39 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.68/0.89          | ((k2_tops_1 @ X39 @ X38)
% 0.68/0.89              = (k7_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.68/0.89                 (k2_pre_topc @ X39 @ X38) @ (k1_tops_1 @ X39 @ X38)))
% 0.68/0.89          | ~ (l1_pre_topc @ X39))),
% 0.68/0.89      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.89               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.89  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.68/0.89            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(dt_k2_tops_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( l1_pre_topc @ A ) & 
% 0.68/0.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.89       ( m1_subset_1 @
% 0.68/0.89         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X34 : $i, X35 : $i]:
% 0.68/0.89         (~ (l1_pre_topc @ X34)
% 0.68/0.89          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.68/0.89          | (m1_subset_1 @ (k2_tops_1 @ X34 @ X35) @ 
% 0.68/0.89             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.68/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.89  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.68/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['7', '8'])).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(redefinition_k4_subset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.68/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.68/0.89       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.68/0.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 0.68/0.89          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 0.68/0.89      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.68/0.89            = (k2_xboole_0 @ sk_B @ X0))
% 0.68/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.89  thf('13', plain,
% 0.68/0.89      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.68/0.89         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['9', '12'])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t65_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( k2_pre_topc @ A @ B ) =
% 0.68/0.89             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (![X42 : $i, X43 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.68/0.89          | ((k2_pre_topc @ X43 @ X42)
% 0.68/0.89              = (k4_subset_1 @ (u1_struct_0 @ X43) @ X42 @ 
% 0.68/0.89                 (k2_tops_1 @ X43 @ X42)))
% 0.68/0.89          | ~ (l1_pre_topc @ X43))),
% 0.68/0.89      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.68/0.89            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.89  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('18', plain,
% 0.68/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.68/0.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('demod', [status(thm)], ['16', '17'])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.68/0.89         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['13', '18'])).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89             (k1_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('split', [status(esa)], ['20'])).
% 0.68/0.89  thf('22', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t69_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( v4_pre_topc @ B @ A ) =>
% 0.68/0.89             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.68/0.89  thf('23', plain,
% 0.68/0.89      (![X44 : $i, X45 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.68/0.89          | (r1_tarski @ (k2_tops_1 @ X45 @ X44) @ X44)
% 0.68/0.89          | ~ (v4_pre_topc @ X44 @ X45)
% 0.68/0.89          | ~ (l1_pre_topc @ X45))),
% 0.68/0.89      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.68/0.89        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.68/0.89      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.89  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.68/0.89        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['21', '26'])).
% 0.68/0.89  thf(t28_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.89  thf('28', plain,
% 0.68/0.89      (![X13 : $i, X14 : $i]:
% 0.68/0.89         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.89  thf('29', plain,
% 0.68/0.89      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.68/0.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.68/0.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.68/0.89  thf('32', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.89  thf(t100_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.89  thf('33', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X5 @ X6)
% 0.68/0.89           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.89  thf('34', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['32', '33'])).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.68/0.89          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.68/0.89             (k2_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['31', '34'])).
% 0.68/0.89  thf(t48_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.89  thf('36', plain,
% 0.68/0.89      (![X20 : $i, X21 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.68/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.68/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.89  thf(t36_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.68/0.89  thf('37', plain,
% 0.68/0.89      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.68/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.89  thf(t12_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.68/0.89  thf('38', plain,
% 0.68/0.89      (![X10 : $i, X11 : $i]:
% 0.68/0.89         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.68/0.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.68/0.89  thf(t1_boole, axiom,
% 0.68/0.89    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.89  thf('40', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['39', '40'])).
% 0.68/0.89  thf('42', plain,
% 0.68/0.89      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['36', '41'])).
% 0.68/0.89  thf('43', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.89  thf('44', plain,
% 0.68/0.89      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['42', '43'])).
% 0.68/0.89  thf('45', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X5 @ X6)
% 0.68/0.89           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.89  thf('46', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (![X20 : $i, X21 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.68/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.68/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.89  thf('48', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.68/0.89           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['46', '47'])).
% 0.68/0.89  thf('49', plain,
% 0.68/0.89      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['42', '43'])).
% 0.68/0.89  thf('50', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['48', '49'])).
% 0.68/0.89  thf('51', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.68/0.89  thf(t3_boole, axiom,
% 0.68/0.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.89  thf('52', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.68/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.89  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['51', '52'])).
% 0.68/0.89  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['50', '53'])).
% 0.68/0.89  thf(d10_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.89  thf('55', plain,
% 0.68/0.89      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('56', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.68/0.89      inference('simplify', [status(thm)], ['55'])).
% 0.68/0.89  thf('57', plain,
% 0.68/0.89      (![X13 : $i, X14 : $i]:
% 0.68/0.89         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.89  thf('58', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.68/0.89  thf('59', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X5 @ X6)
% 0.68/0.89           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.89  thf('60', plain,
% 0.68/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['58', '59'])).
% 0.68/0.89  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['54', '60'])).
% 0.68/0.89  thf('62', plain,
% 0.68/0.89      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['35', '61'])).
% 0.68/0.89  thf(t39_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.89  thf('63', plain,
% 0.68/0.89      (![X17 : $i, X18 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.68/0.89           = (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.68/0.89  thf('64', plain,
% 0.68/0.89      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.68/0.89          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['62', '63'])).
% 0.68/0.89  thf('65', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.68/0.89  thf('66', plain,
% 0.68/0.89      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['64', '65'])).
% 0.68/0.89  thf('67', plain,
% 0.68/0.89      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.68/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['19', '66'])).
% 0.68/0.89  thf('68', plain,
% 0.68/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89              (k1_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('69', plain,
% 0.68/0.89      (~
% 0.68/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.68/0.89       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.68/0.89      inference('split', [status(esa)], ['68'])).
% 0.68/0.89  thf('70', plain,
% 0.68/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.68/0.89         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['13', '18'])).
% 0.68/0.89  thf('71', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(redefinition_k7_subset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.89       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.68/0.89  thf('72', plain,
% 0.68/0.89      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.68/0.89          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 0.68/0.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.68/0.89  thf('73', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.68/0.89           = (k4_xboole_0 @ sk_B @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.68/0.89  thf('74', plain,
% 0.68/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89             (k1_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('split', [status(esa)], ['20'])).
% 0.68/0.89  thf('75', plain,
% 0.68/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('sup+', [status(thm)], ['73', '74'])).
% 0.68/0.89  thf('76', plain,
% 0.68/0.89      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.68/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.89  thf('77', plain,
% 0.68/0.89      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('sup+', [status(thm)], ['75', '76'])).
% 0.68/0.89  thf('78', plain,
% 0.68/0.89      (![X13 : $i, X14 : $i]:
% 0.68/0.89         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.89  thf('79', plain,
% 0.68/0.89      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.68/0.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['77', '78'])).
% 0.68/0.89  thf('80', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.89  thf('81', plain,
% 0.68/0.89      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.68/0.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('demod', [status(thm)], ['79', '80'])).
% 0.68/0.89  thf('82', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['32', '33'])).
% 0.68/0.89  thf('83', plain,
% 0.68/0.89      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.68/0.89          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.68/0.89             (k2_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('sup+', [status(thm)], ['81', '82'])).
% 0.68/0.89  thf('84', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['54', '60'])).
% 0.68/0.89  thf('85', plain,
% 0.68/0.89      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('demod', [status(thm)], ['83', '84'])).
% 0.68/0.89  thf('86', plain,
% 0.68/0.89      (![X17 : $i, X18 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.68/0.89           = (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.68/0.89  thf('87', plain,
% 0.68/0.89      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.68/0.89          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('sup+', [status(thm)], ['85', '86'])).
% 0.68/0.89  thf('88', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.68/0.89  thf('89', plain,
% 0.68/0.89      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('demod', [status(thm)], ['87', '88'])).
% 0.68/0.89  thf('90', plain,
% 0.68/0.89      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('sup+', [status(thm)], ['70', '89'])).
% 0.68/0.89  thf('91', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(fc1_tops_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.68/0.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.89       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.68/0.89  thf('92', plain,
% 0.68/0.89      (![X36 : $i, X37 : $i]:
% 0.68/0.89         (~ (l1_pre_topc @ X36)
% 0.68/0.89          | ~ (v2_pre_topc @ X36)
% 0.68/0.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.68/0.89          | (v4_pre_topc @ (k2_pre_topc @ X36 @ X37) @ X36))),
% 0.68/0.89      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.68/0.89  thf('93', plain,
% 0.68/0.89      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.68/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['91', '92'])).
% 0.68/0.89  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('96', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.68/0.89      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.68/0.89  thf('97', plain,
% 0.68/0.89      (((v4_pre_topc @ sk_B @ sk_A))
% 0.68/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('sup+', [status(thm)], ['90', '96'])).
% 0.68/0.89  thf('98', plain,
% 0.68/0.89      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.68/0.89      inference('split', [status(esa)], ['68'])).
% 0.68/0.89  thf('99', plain,
% 0.68/0.89      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.68/0.89       ~
% 0.68/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['97', '98'])).
% 0.68/0.89  thf('100', plain,
% 0.68/0.89      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.68/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('split', [status(esa)], ['20'])).
% 0.68/0.89  thf('101', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.68/0.89      inference('sat_resolution*', [status(thm)], ['69', '99', '100'])).
% 0.68/0.89  thf('102', plain, (((sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.68/0.89      inference('simpl_trail', [status(thm)], ['67', '101'])).
% 0.68/0.89  thf('103', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.68/0.89           = (k4_xboole_0 @ sk_B @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.68/0.89  thf('104', plain,
% 0.68/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('demod', [status(thm)], ['4', '102', '103'])).
% 0.68/0.89  thf('105', plain,
% 0.68/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89              (k1_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= (~
% 0.68/0.89             (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('split', [status(esa)], ['68'])).
% 0.68/0.89  thf('106', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.68/0.89           = (k4_xboole_0 @ sk_B @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.68/0.89  thf('107', plain,
% 0.68/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.68/0.89         <= (~
% 0.68/0.89             (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.68/0.89      inference('demod', [status(thm)], ['105', '106'])).
% 0.68/0.89  thf('108', plain,
% 0.68/0.89      (~
% 0.68/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('sat_resolution*', [status(thm)], ['69', '99'])).
% 0.68/0.89  thf('109', plain,
% 0.68/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('simpl_trail', [status(thm)], ['107', '108'])).
% 0.68/0.89  thf('110', plain, ($false),
% 0.68/0.89      inference('simplify_reflect-', [status(thm)], ['104', '109'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.75/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
