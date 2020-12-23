%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tgVFG9RKAg

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:52 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 149 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  908 (1942 expanded)
%              Number of equality atoms :   64 ( 112 expanded)
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

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X25 @ X24 ) @ X24 )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
       != X18 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','29','30','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tgVFG9RKAg
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 342 iterations in 0.156s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.62  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.44/0.62  thf(t77_tops_1, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.62             ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.62               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62              ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.62                ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.62                  ( k7_subset_1 @
% 0.44/0.62                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62              (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (~
% 0.44/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.62       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t74_tops_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( k1_tops_1 @ A @ B ) =
% 0.44/0.62             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X26 : $i, X27 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.44/0.62          | ((k1_tops_1 @ X27 @ X26)
% 0.44/0.62              = (k7_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.44/0.62                 (k2_tops_1 @ X27 @ X26)))
% 0.44/0.62          | ~ (l1_pre_topc @ X27))),
% 0.44/0.62      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.44/0.62            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.62  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k7_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.44/0.62          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (((k1_tops_1 @ sk_A @ sk_B)
% 0.44/0.62         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.44/0.62  thf(t48_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.44/0.62           = (k3_xboole_0 @ X10 @ X11))),
% 0.44/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.44/0.62         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62             (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.62        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.62      inference('split', [status(esa)], ['12'])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t69_tops_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( v4_pre_topc @ B @ A ) =>
% 0.44/0.62             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X24 : $i, X25 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.62          | (r1_tarski @ (k2_tops_1 @ X25 @ X24) @ X24)
% 0.44/0.62          | ~ (v4_pre_topc @ X24 @ X25)
% 0.44/0.62          | ~ (l1_pre_topc @ X25))),
% 0.44/0.62      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.44/0.62        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.62  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.44/0.62        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.44/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.44/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '18'])).
% 0.44/0.62  thf(t28_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (![X6 : $i, X7 : $i]:
% 0.44/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.44/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.44/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['11', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62              (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.44/0.62             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['24', '27'])).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.62       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.62       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.62      inference('split', [status(esa)], ['12'])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t65_tops_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( k2_pre_topc @ A @ B ) =
% 0.44/0.62             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (![X22 : $i, X23 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.44/0.62          | ((k2_pre_topc @ X23 @ X22)
% 0.44/0.62              = (k4_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.44/0.62                 (k2_tops_1 @ X23 @ X22)))
% 0.44/0.62          | ~ (l1_pre_topc @ X23))),
% 0.44/0.62      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.62            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.62  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.62         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(dt_k2_tops_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.44/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62       ( m1_subset_1 @
% 0.44/0.62         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      (![X20 : $i, X21 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.62          | (m1_subset_1 @ (k2_tops_1 @ X20 @ X21) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k4_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.62       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.44/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.44/0.62          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.62            = (k2_xboole_0 @ sk_B @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.62         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['40', '43'])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.62         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['35', '44'])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62             (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.62      inference('split', [status(esa)], ['12'])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['46', '47'])).
% 0.44/0.62  thf(t36_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.44/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.62  thf(t12_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i]:
% 0.44/0.62         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.44/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.44/0.62  thf('52', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.62  thf('53', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.44/0.62  thf('54', plain,
% 0.44/0.62      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.44/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['48', '53'])).
% 0.44/0.62  thf('55', plain,
% 0.44/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.44/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['45', '54'])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t52_pre_topc, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.44/0.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.44/0.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.44/0.62  thf('57', plain,
% 0.44/0.62      (![X18 : $i, X19 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.44/0.62          | ~ (v2_pre_topc @ X19)
% 0.44/0.62          | ((k2_pre_topc @ X19 @ X18) != (X18))
% 0.44/0.63          | (v4_pre_topc @ X18 @ X19)
% 0.44/0.63          | ~ (l1_pre_topc @ X19))),
% 0.44/0.63      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.44/0.63  thf('58', plain,
% 0.44/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | (v4_pre_topc @ sk_B @ sk_A)
% 0.44/0.63        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.44/0.63        | ~ (v2_pre_topc @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.63  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('61', plain,
% 0.44/0.63      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.63  thf('62', plain,
% 0.44/0.63      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.44/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['55', '61'])).
% 0.44/0.63  thf('63', plain,
% 0.44/0.63      (((v4_pre_topc @ sk_B @ sk_A))
% 0.44/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.63      inference('simplify', [status(thm)], ['62'])).
% 0.44/0.63  thf('64', plain,
% 0.44/0.63      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf('65', plain,
% 0.44/0.63      (~
% 0.44/0.63       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.63       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.63  thf('66', plain, ($false),
% 0.44/0.63      inference('sat_resolution*', [status(thm)], ['1', '29', '30', '65'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
