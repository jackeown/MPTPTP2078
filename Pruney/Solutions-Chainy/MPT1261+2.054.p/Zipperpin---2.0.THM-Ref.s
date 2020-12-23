%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LgfaXHcCWI

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:45 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 322 expanded)
%              Number of leaves         :   42 ( 115 expanded)
%              Depth                    :   20
%              Number of atoms          : 1348 (3079 expanded)
%              Number of equality atoms :  114 ( 245 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k1_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X30 @ X32 )
        = ( k4_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('15',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X47 @ X46 ) @ X46 )
      | ~ ( v4_pre_topc @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['42','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k4_subset_1 @ X28 @ X27 @ X29 )
        = ( k2_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('72',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','75'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('80',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('84',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('87',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','91'])).

thf('93',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('96',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','91'])).

thf('100',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['58','102'])).

thf('104',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('106',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 @ ( k2_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['104','109'])).

thf('111',plain,(
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

thf('112',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_pre_topc @ X39 )
      | ( ( k2_pre_topc @ X39 @ X38 )
       != X38 )
      | ( v4_pre_topc @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LgfaXHcCWI
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.53/1.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.53/1.73  % Solved by: fo/fo7.sh
% 1.53/1.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.73  % done 4049 iterations in 1.279s
% 1.53/1.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.53/1.73  % SZS output start Refutation
% 1.53/1.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.53/1.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.53/1.73  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.73  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.53/1.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.53/1.73  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.53/1.73  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.53/1.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.53/1.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.53/1.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.53/1.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.53/1.73  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.53/1.73  thf(sk_B_type, type, sk_B: $i).
% 1.53/1.73  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.53/1.73  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.53/1.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.53/1.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.53/1.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.53/1.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.53/1.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.53/1.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.53/1.73  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.53/1.73  thf(t77_tops_1, conjecture,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.73           ( ( v4_pre_topc @ B @ A ) <=>
% 1.53/1.73             ( ( k2_tops_1 @ A @ B ) =
% 1.53/1.73               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.53/1.73  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.73    (~( ![A:$i]:
% 1.53/1.73        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.73          ( ![B:$i]:
% 1.53/1.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.73              ( ( v4_pre_topc @ B @ A ) <=>
% 1.53/1.73                ( ( k2_tops_1 @ A @ B ) =
% 1.53/1.73                  ( k7_subset_1 @
% 1.53/1.73                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.53/1.73    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.53/1.73  thf('0', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73              (k1_tops_1 @ sk_A @ sk_B)))
% 1.53/1.73        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('1', plain,
% 1.53/1.73      (~
% 1.53/1.73       (((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.53/1.73       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.53/1.73      inference('split', [status(esa)], ['0'])).
% 1.53/1.73  thf('2', plain,
% 1.53/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(t74_tops_1, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( l1_pre_topc @ A ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.73           ( ( k1_tops_1 @ A @ B ) =
% 1.53/1.73             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.53/1.73  thf('3', plain,
% 1.53/1.73      (![X48 : $i, X49 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.53/1.73          | ((k1_tops_1 @ X49 @ X48)
% 1.53/1.73              = (k7_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 1.53/1.73                 (k2_tops_1 @ X49 @ X48)))
% 1.53/1.73          | ~ (l1_pre_topc @ X49))),
% 1.53/1.73      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.53/1.73  thf('4', plain,
% 1.53/1.73      ((~ (l1_pre_topc @ sk_A)
% 1.53/1.73        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.53/1.73            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['2', '3'])).
% 1.53/1.73  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('6', plain,
% 1.53/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(redefinition_k7_subset_1, axiom,
% 1.53/1.73    (![A:$i,B:$i,C:$i]:
% 1.53/1.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.73       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.53/1.73  thf('7', plain,
% 1.53/1.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 1.53/1.73          | ((k7_subset_1 @ X31 @ X30 @ X32) = (k4_xboole_0 @ X30 @ X32)))),
% 1.53/1.73      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.53/1.73  thf('8', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.53/1.73           = (k4_xboole_0 @ sk_B @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['6', '7'])).
% 1.53/1.73  thf('9', plain,
% 1.53/1.73      (((k1_tops_1 @ sk_A @ sk_B)
% 1.53/1.73         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.53/1.73      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.53/1.73  thf(t48_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.53/1.73  thf('10', plain,
% 1.53/1.73      (![X13 : $i, X14 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.53/1.73           = (k3_xboole_0 @ X13 @ X14))),
% 1.53/1.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.53/1.73  thf('11', plain,
% 1.53/1.73      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.53/1.73         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.53/1.73      inference('sup+', [status(thm)], ['9', '10'])).
% 1.53/1.73  thf('12', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73             (k1_tops_1 @ sk_A @ sk_B)))
% 1.53/1.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('13', plain,
% 1.53/1.73      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.53/1.73      inference('split', [status(esa)], ['12'])).
% 1.53/1.73  thf('14', plain,
% 1.53/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(t69_tops_1, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( l1_pre_topc @ A ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.73           ( ( v4_pre_topc @ B @ A ) =>
% 1.53/1.73             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.53/1.73  thf('15', plain,
% 1.53/1.73      (![X46 : $i, X47 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.53/1.73          | (r1_tarski @ (k2_tops_1 @ X47 @ X46) @ X46)
% 1.53/1.73          | ~ (v4_pre_topc @ X46 @ X47)
% 1.53/1.73          | ~ (l1_pre_topc @ X47))),
% 1.53/1.73      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.53/1.73  thf('16', plain,
% 1.53/1.73      ((~ (l1_pre_topc @ sk_A)
% 1.53/1.73        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.53/1.73        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['14', '15'])).
% 1.53/1.73  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('18', plain,
% 1.53/1.73      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.53/1.73        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.53/1.73      inference('demod', [status(thm)], ['16', '17'])).
% 1.53/1.73  thf('19', plain,
% 1.53/1.73      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.53/1.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['13', '18'])).
% 1.53/1.73  thf(t28_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.53/1.73  thf('20', plain,
% 1.53/1.73      (![X7 : $i, X8 : $i]:
% 1.53/1.73         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.53/1.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.53/1.73  thf('21', plain,
% 1.53/1.73      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.53/1.73          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.53/1.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['19', '20'])).
% 1.53/1.73  thf(commutativity_k2_tarski, axiom,
% 1.53/1.73    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.53/1.73  thf('22', plain,
% 1.53/1.73      (![X17 : $i, X18 : $i]:
% 1.53/1.73         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 1.53/1.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.53/1.73  thf(t12_setfam_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.53/1.73  thf('23', plain,
% 1.53/1.73      (![X33 : $i, X34 : $i]:
% 1.53/1.73         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 1.53/1.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.53/1.73  thf('24', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('sup+', [status(thm)], ['22', '23'])).
% 1.53/1.73  thf('25', plain,
% 1.53/1.73      (![X33 : $i, X34 : $i]:
% 1.53/1.73         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 1.53/1.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.53/1.73  thf('26', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('sup+', [status(thm)], ['24', '25'])).
% 1.53/1.73  thf('27', plain,
% 1.53/1.73      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.53/1.73          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.53/1.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.53/1.73      inference('demod', [status(thm)], ['21', '26'])).
% 1.53/1.73  thf('28', plain,
% 1.53/1.73      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.53/1.73          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.53/1.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.53/1.73      inference('sup+', [status(thm)], ['11', '27'])).
% 1.53/1.73  thf('29', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.53/1.73           = (k4_xboole_0 @ sk_B @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['6', '7'])).
% 1.53/1.73  thf('30', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73              (k1_tops_1 @ sk_A @ sk_B))))
% 1.53/1.73         <= (~
% 1.53/1.73             (((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('split', [status(esa)], ['0'])).
% 1.53/1.73  thf('31', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.53/1.73         <= (~
% 1.53/1.73             (((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['29', '30'])).
% 1.53/1.73  thf('32', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.53/1.73         <= (~
% 1.53/1.73             (((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.53/1.73             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['28', '31'])).
% 1.53/1.73  thf('33', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.53/1.73       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.53/1.73      inference('simplify', [status(thm)], ['32'])).
% 1.53/1.73  thf('34', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.53/1.73       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.53/1.73      inference('split', [status(esa)], ['12'])).
% 1.53/1.73  thf('35', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.53/1.73           = (k4_xboole_0 @ sk_B @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['6', '7'])).
% 1.53/1.73  thf('36', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73             (k1_tops_1 @ sk_A @ sk_B))))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('split', [status(esa)], ['12'])).
% 1.53/1.73  thf('37', plain,
% 1.53/1.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('sup+', [status(thm)], ['35', '36'])).
% 1.53/1.73  thf(t36_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.53/1.73  thf('38', plain,
% 1.53/1.73      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.53/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.53/1.73  thf('39', plain,
% 1.53/1.73      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('sup+', [status(thm)], ['37', '38'])).
% 1.53/1.73  thf('40', plain,
% 1.53/1.73      (![X7 : $i, X8 : $i]:
% 1.53/1.73         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.53/1.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.53/1.73  thf('41', plain,
% 1.53/1.73      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.53/1.73          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['39', '40'])).
% 1.53/1.73  thf('42', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('sup+', [status(thm)], ['24', '25'])).
% 1.53/1.73  thf('43', plain,
% 1.53/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(t3_subset, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.53/1.73  thf('44', plain,
% 1.53/1.73      (![X35 : $i, X36 : $i]:
% 1.53/1.73         ((r1_tarski @ X35 @ X36) | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.73  thf('45', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['43', '44'])).
% 1.53/1.73  thf('46', plain,
% 1.53/1.73      (![X13 : $i, X14 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.53/1.73           = (k3_xboole_0 @ X13 @ X14))),
% 1.53/1.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.53/1.73  thf('47', plain,
% 1.53/1.73      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.53/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.53/1.73  thf('48', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.53/1.73      inference('sup+', [status(thm)], ['46', '47'])).
% 1.53/1.73  thf(t1_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i,C:$i]:
% 1.53/1.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.53/1.73       ( r1_tarski @ A @ C ) ))).
% 1.53/1.73  thf('49', plain,
% 1.53/1.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.53/1.73         (~ (r1_tarski @ X4 @ X5)
% 1.53/1.73          | ~ (r1_tarski @ X5 @ X6)
% 1.53/1.73          | (r1_tarski @ X4 @ X6))),
% 1.53/1.73      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.53/1.73  thf('50', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.73         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.53/1.73      inference('sup-', [status(thm)], ['48', '49'])).
% 1.53/1.73  thf('51', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['45', '50'])).
% 1.53/1.73  thf('52', plain,
% 1.53/1.73      (![X35 : $i, X37 : $i]:
% 1.53/1.73         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 1.53/1.73      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.73  thf('53', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 1.53/1.73          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['51', '52'])).
% 1.53/1.73  thf('54', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.53/1.73          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('sup+', [status(thm)], ['42', '53'])).
% 1.53/1.73  thf('55', plain,
% 1.53/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(redefinition_k4_subset_1, axiom,
% 1.53/1.73    (![A:$i,B:$i,C:$i]:
% 1.53/1.73     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.53/1.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.53/1.73       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.53/1.73  thf('56', plain,
% 1.53/1.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 1.53/1.73          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 1.53/1.73          | ((k4_subset_1 @ X28 @ X27 @ X29) = (k2_xboole_0 @ X27 @ X29)))),
% 1.53/1.73      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.53/1.73  thf('57', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.53/1.73            = (k2_xboole_0 @ sk_B @ X0))
% 1.53/1.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['55', '56'])).
% 1.53/1.73  thf('58', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73           (k3_xboole_0 @ X0 @ sk_B))
% 1.53/1.73           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['54', '57'])).
% 1.53/1.73  thf('59', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('sup+', [status(thm)], ['24', '25'])).
% 1.53/1.73  thf('60', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.53/1.73      inference('sup+', [status(thm)], ['46', '47'])).
% 1.53/1.73  thf('61', plain,
% 1.53/1.73      (![X7 : $i, X8 : $i]:
% 1.53/1.73         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.53/1.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.53/1.73  thf('62', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.53/1.73           = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('sup-', [status(thm)], ['60', '61'])).
% 1.53/1.73  thf('63', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('sup+', [status(thm)], ['24', '25'])).
% 1.53/1.73  thf('64', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.53/1.73           = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('demod', [status(thm)], ['62', '63'])).
% 1.53/1.73  thf('65', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.53/1.73      inference('sup+', [status(thm)], ['24', '25'])).
% 1.53/1.73  thf(t100_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.53/1.73  thf('66', plain,
% 1.53/1.73      (![X1 : $i, X2 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X1 @ X2)
% 1.53/1.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.53/1.73  thf('67', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X0 @ X1)
% 1.53/1.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.73      inference('sup+', [status(thm)], ['65', '66'])).
% 1.53/1.73  thf('68', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.53/1.73           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.73      inference('sup+', [status(thm)], ['64', '67'])).
% 1.53/1.73  thf(idempotence_k3_xboole_0, axiom,
% 1.53/1.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.53/1.73  thf('69', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.53/1.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.53/1.73  thf('70', plain,
% 1.53/1.73      (![X1 : $i, X2 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X1 @ X2)
% 1.53/1.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.53/1.73  thf('71', plain,
% 1.53/1.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['69', '70'])).
% 1.53/1.73  thf(t1_boole, axiom,
% 1.53/1.73    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.53/1.73  thf('72', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 1.53/1.73      inference('cnf', [status(esa)], [t1_boole])).
% 1.53/1.73  thf(t46_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.53/1.73  thf('73', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 1.53/1.73      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.53/1.73  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['72', '73'])).
% 1.53/1.73  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['71', '74'])).
% 1.53/1.73  thf('76', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.53/1.73      inference('demod', [status(thm)], ['68', '75'])).
% 1.53/1.73  thf(t98_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.53/1.73  thf('77', plain,
% 1.53/1.73      (![X15 : $i, X16 : $i]:
% 1.53/1.73         ((k2_xboole_0 @ X15 @ X16)
% 1.53/1.73           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.53/1.73  thf('78', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.53/1.73           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['76', '77'])).
% 1.53/1.73  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['72', '73'])).
% 1.53/1.73  thf('80', plain,
% 1.53/1.73      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.53/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.53/1.73  thf('81', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.53/1.73      inference('sup+', [status(thm)], ['79', '80'])).
% 1.53/1.73  thf('82', plain,
% 1.53/1.73      (![X35 : $i, X37 : $i]:
% 1.53/1.73         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 1.53/1.73      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.73  thf('83', plain,
% 1.53/1.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['81', '82'])).
% 1.53/1.73  thf(d5_subset_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.73       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.53/1.73  thf('84', plain,
% 1.53/1.73      (![X21 : $i, X22 : $i]:
% 1.53/1.73         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 1.53/1.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.53/1.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.53/1.73  thf('85', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['83', '84'])).
% 1.53/1.73  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['72', '73'])).
% 1.53/1.73  thf('87', plain,
% 1.53/1.73      (![X13 : $i, X14 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.53/1.73           = (k3_xboole_0 @ X13 @ X14))),
% 1.53/1.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.53/1.73  thf('88', plain,
% 1.53/1.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['86', '87'])).
% 1.53/1.73  thf('89', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['83', '84'])).
% 1.53/1.73  thf('90', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.53/1.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.53/1.73  thf('91', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.53/1.73      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.53/1.73  thf('92', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('demod', [status(thm)], ['85', '91'])).
% 1.53/1.73  thf('93', plain,
% 1.53/1.73      (![X13 : $i, X14 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.53/1.73           = (k3_xboole_0 @ X13 @ X14))),
% 1.53/1.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.53/1.73  thf('94', plain,
% 1.53/1.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['92', '93'])).
% 1.53/1.73  thf('95', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['72', '73'])).
% 1.53/1.73  thf('96', plain,
% 1.53/1.73      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('demod', [status(thm)], ['94', '95'])).
% 1.53/1.73  thf('97', plain,
% 1.53/1.73      (![X1 : $i, X2 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X1 @ X2)
% 1.53/1.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.53/1.73  thf('98', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['96', '97'])).
% 1.53/1.73  thf('99', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('demod', [status(thm)], ['85', '91'])).
% 1.53/1.73  thf('100', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['98', '99'])).
% 1.53/1.73  thf('101', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.53/1.73      inference('demod', [status(thm)], ['78', '100'])).
% 1.53/1.73  thf('102', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.53/1.73      inference('sup+', [status(thm)], ['59', '101'])).
% 1.53/1.73  thf('103', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73           (k3_xboole_0 @ X0 @ sk_B)) = (sk_B))),
% 1.53/1.73      inference('demod', [status(thm)], ['58', '102'])).
% 1.53/1.73  thf('104', plain,
% 1.53/1.73      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.53/1.73          = (sk_B)))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('sup+', [status(thm)], ['41', '103'])).
% 1.53/1.73  thf('105', plain,
% 1.53/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(t65_tops_1, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( l1_pre_topc @ A ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.73           ( ( k2_pre_topc @ A @ B ) =
% 1.53/1.73             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.53/1.73  thf('106', plain,
% 1.53/1.73      (![X44 : $i, X45 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.53/1.73          | ((k2_pre_topc @ X45 @ X44)
% 1.53/1.73              = (k4_subset_1 @ (u1_struct_0 @ X45) @ X44 @ 
% 1.53/1.73                 (k2_tops_1 @ X45 @ X44)))
% 1.53/1.73          | ~ (l1_pre_topc @ X45))),
% 1.53/1.73      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.53/1.73  thf('107', plain,
% 1.53/1.73      ((~ (l1_pre_topc @ sk_A)
% 1.53/1.73        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.53/1.73            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['105', '106'])).
% 1.53/1.73  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('109', plain,
% 1.53/1.73      (((k2_pre_topc @ sk_A @ sk_B)
% 1.53/1.73         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.53/1.73      inference('demod', [status(thm)], ['107', '108'])).
% 1.53/1.73  thf('110', plain,
% 1.53/1.73      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('sup+', [status(thm)], ['104', '109'])).
% 1.53/1.73  thf('111', plain,
% 1.53/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(t52_pre_topc, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( l1_pre_topc @ A ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.73           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.53/1.73             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.53/1.73               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.53/1.73  thf('112', plain,
% 1.53/1.73      (![X38 : $i, X39 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.53/1.73          | ~ (v2_pre_topc @ X39)
% 1.53/1.73          | ((k2_pre_topc @ X39 @ X38) != (X38))
% 1.53/1.73          | (v4_pre_topc @ X38 @ X39)
% 1.53/1.73          | ~ (l1_pre_topc @ X39))),
% 1.53/1.73      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.53/1.73  thf('113', plain,
% 1.53/1.73      ((~ (l1_pre_topc @ sk_A)
% 1.53/1.73        | (v4_pre_topc @ sk_B @ sk_A)
% 1.53/1.73        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.53/1.73        | ~ (v2_pre_topc @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['111', '112'])).
% 1.53/1.73  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('116', plain,
% 1.53/1.73      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.53/1.73      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.53/1.73  thf('117', plain,
% 1.53/1.73      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['110', '116'])).
% 1.53/1.73  thf('118', plain,
% 1.53/1.73      (((v4_pre_topc @ sk_B @ sk_A))
% 1.53/1.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.53/1.73      inference('simplify', [status(thm)], ['117'])).
% 1.53/1.73  thf('119', plain,
% 1.53/1.73      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.53/1.73      inference('split', [status(esa)], ['0'])).
% 1.53/1.73  thf('120', plain,
% 1.53/1.73      (~
% 1.53/1.73       (((k2_tops_1 @ sk_A @ sk_B)
% 1.53/1.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.53/1.73             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.53/1.73       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['118', '119'])).
% 1.53/1.73  thf('121', plain, ($false),
% 1.53/1.73      inference('sat_resolution*', [status(thm)], ['1', '33', '34', '120'])).
% 1.53/1.73  
% 1.53/1.73  % SZS output end Refutation
% 1.53/1.73  
% 1.53/1.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
