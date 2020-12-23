%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iMvv2uUumS

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:57 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 320 expanded)
%              Number of leaves         :   42 ( 112 expanded)
%              Depth                    :   17
%              Number of atoms          : 1409 (3370 expanded)
%              Number of equality atoms :  116 ( 241 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( ( k1_tops_1 @ X55 @ X54 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 @ ( k2_tops_1 @ X55 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
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
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X53 @ X52 ) @ X52 )
      | ~ ( v4_pre_topc @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('32',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_pre_topc @ X51 @ X50 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 @ ( k2_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('61',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('69',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('79',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','78','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','85'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X41: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r1_tarski @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('92',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X26 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('93',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = X23 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('94',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','78','83'])).

thf('99',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('100',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_subset_1 @ X37 @ X38 @ ( k3_subset_1 @ X37 @ X38 ) )
        = ( k2_subset_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('101',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = X23 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('102',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_subset_1 @ X37 @ X38 @ ( k3_subset_1 @ X37 @ X38 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('105',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('106',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['98','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['97','110'])).

thf('112',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','111'])).

thf('113',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','112'])).

thf('114',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','113'])).

thf('115',plain,(
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

thf('116',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_pre_topc @ X45 )
      | ( ( k2_pre_topc @ X45 @ X44 )
       != X44 )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','29','30','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iMvv2uUumS
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:47:09 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 1.15/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.35  % Solved by: fo/fo7.sh
% 1.15/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.35  % done 2229 iterations in 0.921s
% 1.15/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.35  % SZS output start Refutation
% 1.15/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.35  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.15/1.35  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.15/1.35  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.15/1.35  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.15/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.15/1.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.15/1.35  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.15/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.35  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.15/1.35  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.35  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.15/1.35  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.15/1.35  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.15/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.35  thf(t77_tops_1, conjecture,
% 1.15/1.35    (![A:$i]:
% 1.15/1.35     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.15/1.35       ( ![B:$i]:
% 1.15/1.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.35           ( ( v4_pre_topc @ B @ A ) <=>
% 1.15/1.35             ( ( k2_tops_1 @ A @ B ) =
% 1.15/1.35               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.15/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.35    (~( ![A:$i]:
% 1.15/1.35        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.15/1.35          ( ![B:$i]:
% 1.15/1.35            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.35              ( ( v4_pre_topc @ B @ A ) <=>
% 1.15/1.35                ( ( k2_tops_1 @ A @ B ) =
% 1.15/1.35                  ( k7_subset_1 @
% 1.15/1.35                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.15/1.35    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.15/1.35  thf('0', plain,
% 1.15/1.35      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.35          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.35              (k1_tops_1 @ sk_A @ sk_B)))
% 1.15/1.35        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('1', plain,
% 1.15/1.35      (~
% 1.15/1.35       (((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.35          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.35             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.15/1.35       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.15/1.35      inference('split', [status(esa)], ['0'])).
% 1.15/1.35  thf('2', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(t74_tops_1, axiom,
% 1.15/1.35    (![A:$i]:
% 1.15/1.35     ( ( l1_pre_topc @ A ) =>
% 1.15/1.35       ( ![B:$i]:
% 1.15/1.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.35           ( ( k1_tops_1 @ A @ B ) =
% 1.15/1.35             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.15/1.35  thf('3', plain,
% 1.15/1.35      (![X54 : $i, X55 : $i]:
% 1.15/1.35         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 1.15/1.35          | ((k1_tops_1 @ X55 @ X54)
% 1.15/1.35              = (k7_subset_1 @ (u1_struct_0 @ X55) @ X54 @ 
% 1.15/1.35                 (k2_tops_1 @ X55 @ X54)))
% 1.15/1.35          | ~ (l1_pre_topc @ X55))),
% 1.15/1.35      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.15/1.35  thf('4', plain,
% 1.15/1.35      ((~ (l1_pre_topc @ sk_A)
% 1.15/1.35        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.15/1.35            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.35               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('6', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(redefinition_k7_subset_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.35       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.15/1.35  thf('7', plain,
% 1.15/1.35      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.15/1.35         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 1.15/1.35          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.15/1.35  thf('8', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.15/1.35           = (k4_xboole_0 @ sk_B @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.35  thf('9', plain,
% 1.15/1.35      (((k1_tops_1 @ sk_A @ sk_B)
% 1.15/1.35         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.15/1.35  thf(t48_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.15/1.35  thf('10', plain,
% 1.15/1.35      (![X21 : $i, X22 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.15/1.35           = (k3_xboole_0 @ X21 @ X22))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf('11', plain,
% 1.15/1.35      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.15/1.35         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['9', '10'])).
% 1.15/1.36  thf('12', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36             (k1_tops_1 @ sk_A @ sk_B)))
% 1.15/1.36        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('13', plain,
% 1.15/1.36      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.15/1.36      inference('split', [status(esa)], ['12'])).
% 1.15/1.36  thf('14', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(t69_tops_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( l1_pre_topc @ A ) =>
% 1.15/1.36       ( ![B:$i]:
% 1.15/1.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.36           ( ( v4_pre_topc @ B @ A ) =>
% 1.15/1.36             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.15/1.36  thf('15', plain,
% 1.15/1.36      (![X52 : $i, X53 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.15/1.36          | (r1_tarski @ (k2_tops_1 @ X53 @ X52) @ X52)
% 1.15/1.36          | ~ (v4_pre_topc @ X52 @ X53)
% 1.15/1.36          | ~ (l1_pre_topc @ X53))),
% 1.15/1.36      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.15/1.36  thf('16', plain,
% 1.15/1.36      ((~ (l1_pre_topc @ sk_A)
% 1.15/1.36        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.15/1.36        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.15/1.36      inference('sup-', [status(thm)], ['14', '15'])).
% 1.15/1.36  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('18', plain,
% 1.15/1.36      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.15/1.36        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.15/1.36      inference('demod', [status(thm)], ['16', '17'])).
% 1.15/1.36  thf('19', plain,
% 1.15/1.36      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.15/1.36         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['13', '18'])).
% 1.15/1.36  thf(t28_xboole_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.15/1.36  thf('20', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.36  thf('21', plain,
% 1.15/1.36      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.15/1.36          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.15/1.36         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['19', '20'])).
% 1.15/1.36  thf(commutativity_k3_xboole_0, axiom,
% 1.15/1.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.15/1.36  thf('22', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('23', plain,
% 1.15/1.36      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.15/1.36          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.15/1.36         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.15/1.36      inference('demod', [status(thm)], ['21', '22'])).
% 1.15/1.36  thf('24', plain,
% 1.15/1.36      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.15/1.36          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.15/1.36         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['11', '23'])).
% 1.15/1.36  thf('25', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.15/1.36           = (k4_xboole_0 @ sk_B @ X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.36  thf('26', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36              (k1_tops_1 @ sk_A @ sk_B))))
% 1.15/1.36         <= (~
% 1.15/1.36             (((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('split', [status(esa)], ['0'])).
% 1.15/1.36  thf('27', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.15/1.36         <= (~
% 1.15/1.36             (((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['25', '26'])).
% 1.15/1.36  thf('28', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.15/1.36         <= (~
% 1.15/1.36             (((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.15/1.36             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['24', '27'])).
% 1.15/1.36  thf('29', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.15/1.36       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.15/1.36      inference('simplify', [status(thm)], ['28'])).
% 1.15/1.36  thf('30', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.15/1.36       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.15/1.36      inference('split', [status(esa)], ['12'])).
% 1.15/1.36  thf('31', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(dt_k2_tops_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( ( l1_pre_topc @ A ) & 
% 1.15/1.36         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.15/1.36       ( m1_subset_1 @
% 1.15/1.36         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.15/1.36  thf('32', plain,
% 1.15/1.36      (![X46 : $i, X47 : $i]:
% 1.15/1.36         (~ (l1_pre_topc @ X46)
% 1.15/1.36          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.15/1.36          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 1.15/1.36             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.15/1.36  thf('33', plain,
% 1.15/1.36      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.15/1.36         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.15/1.36        | ~ (l1_pre_topc @ sk_A))),
% 1.15/1.36      inference('sup-', [status(thm)], ['31', '32'])).
% 1.15/1.36  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('35', plain,
% 1.15/1.36      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.15/1.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.36      inference('demod', [status(thm)], ['33', '34'])).
% 1.15/1.36  thf('36', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(redefinition_k4_subset_1, axiom,
% 1.15/1.36    (![A:$i,B:$i,C:$i]:
% 1.15/1.36     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.15/1.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.15/1.36       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.15/1.36  thf('37', plain,
% 1.15/1.36      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 1.15/1.36          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 1.15/1.36          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.15/1.36  thf('38', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.15/1.36            = (k2_xboole_0 @ sk_B @ X0))
% 1.15/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['36', '37'])).
% 1.15/1.36  thf('39', plain,
% 1.15/1.36      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.15/1.36         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['35', '38'])).
% 1.15/1.36  thf('40', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(t65_tops_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( l1_pre_topc @ A ) =>
% 1.15/1.36       ( ![B:$i]:
% 1.15/1.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.36           ( ( k2_pre_topc @ A @ B ) =
% 1.15/1.36             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.15/1.36  thf('41', plain,
% 1.15/1.36      (![X50 : $i, X51 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 1.15/1.36          | ((k2_pre_topc @ X51 @ X50)
% 1.15/1.36              = (k4_subset_1 @ (u1_struct_0 @ X51) @ X50 @ 
% 1.15/1.36                 (k2_tops_1 @ X51 @ X50)))
% 1.15/1.36          | ~ (l1_pre_topc @ X51))),
% 1.15/1.36      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.15/1.36  thf('42', plain,
% 1.15/1.36      ((~ (l1_pre_topc @ sk_A)
% 1.15/1.36        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.15/1.36            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['40', '41'])).
% 1.15/1.36  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('44', plain,
% 1.15/1.36      (((k2_pre_topc @ sk_A @ sk_B)
% 1.15/1.36         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('demod', [status(thm)], ['42', '43'])).
% 1.15/1.36  thf('45', plain,
% 1.15/1.36      (((k2_pre_topc @ sk_A @ sk_B)
% 1.15/1.36         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['39', '44'])).
% 1.15/1.36  thf('46', plain,
% 1.15/1.36      (((k1_tops_1 @ sk_A @ sk_B)
% 1.15/1.36         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.15/1.36  thf(t36_xboole_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.15/1.36  thf('47', plain,
% 1.15/1.36      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 1.15/1.36      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.15/1.36  thf('48', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.15/1.36      inference('sup+', [status(thm)], ['46', '47'])).
% 1.15/1.36  thf('49', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.36  thf('50', plain,
% 1.15/1.36      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.15/1.36         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.15/1.36      inference('sup-', [status(thm)], ['48', '49'])).
% 1.15/1.36  thf('51', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('52', plain,
% 1.15/1.36      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.15/1.36         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.15/1.36      inference('demod', [status(thm)], ['50', '51'])).
% 1.15/1.36  thf(t100_xboole_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.15/1.36  thf('53', plain,
% 1.15/1.36      (![X11 : $i, X12 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X11 @ X12)
% 1.15/1.36           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.15/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.36  thf('54', plain,
% 1.15/1.36      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.15/1.36         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.36  thf('55', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.15/1.36           = (k4_xboole_0 @ sk_B @ X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.36  thf('56', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36             (k1_tops_1 @ sk_A @ sk_B))))
% 1.15/1.36         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('split', [status(esa)], ['12'])).
% 1.15/1.36  thf('57', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.15/1.36         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('sup+', [status(thm)], ['55', '56'])).
% 1.15/1.36  thf('58', plain,
% 1.15/1.36      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.15/1.36         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('sup+', [status(thm)], ['54', '57'])).
% 1.15/1.36  thf('59', plain,
% 1.15/1.36      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.15/1.36         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.36  thf('60', plain,
% 1.15/1.36      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 1.15/1.36      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.15/1.36  thf('61', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.36  thf('62', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.15/1.36           = (k4_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('sup-', [status(thm)], ['60', '61'])).
% 1.15/1.36  thf('63', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('64', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.15/1.36           = (k4_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('demod', [status(thm)], ['62', '63'])).
% 1.15/1.36  thf('65', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('66', plain,
% 1.15/1.36      (![X11 : $i, X12 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X11 @ X12)
% 1.15/1.36           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.15/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.36  thf('67', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.36           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['65', '66'])).
% 1.15/1.36  thf('68', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.15/1.36           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['64', '67'])).
% 1.15/1.36  thf(t3_boole, axiom,
% 1.15/1.36    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.15/1.36  thf('69', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.15/1.36      inference('cnf', [status(esa)], [t3_boole])).
% 1.15/1.36  thf('70', plain,
% 1.15/1.36      (![X21 : $i, X22 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.15/1.36           = (k3_xboole_0 @ X21 @ X22))),
% 1.15/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.36  thf('71', plain,
% 1.15/1.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['69', '70'])).
% 1.15/1.36  thf('72', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.15/1.36      inference('cnf', [status(esa)], [t3_boole])).
% 1.15/1.36  thf('73', plain,
% 1.15/1.36      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 1.15/1.36      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.15/1.36  thf('74', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.15/1.36      inference('sup+', [status(thm)], ['72', '73'])).
% 1.15/1.36  thf('75', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.36  thf('76', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['74', '75'])).
% 1.15/1.36  thf('77', plain,
% 1.15/1.36      (![X11 : $i, X12 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X11 @ X12)
% 1.15/1.36           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.15/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.36  thf('78', plain,
% 1.15/1.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['76', '77'])).
% 1.15/1.36  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.15/1.36  thf('79', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 1.15/1.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.15/1.36  thf('80', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.36  thf('81', plain,
% 1.15/1.36      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['79', '80'])).
% 1.15/1.36  thf('82', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('83', plain,
% 1.15/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['81', '82'])).
% 1.15/1.36  thf('84', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.36      inference('demod', [status(thm)], ['71', '78', '83'])).
% 1.15/1.36  thf('85', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.15/1.36      inference('demod', [status(thm)], ['68', '84'])).
% 1.15/1.36  thf('86', plain,
% 1.15/1.36      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 1.15/1.36         = (k1_xboole_0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['59', '85'])).
% 1.15/1.36  thf(t39_xboole_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.15/1.36  thf('87', plain,
% 1.15/1.36      (![X18 : $i, X19 : $i]:
% 1.15/1.36         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 1.15/1.36           = (k2_xboole_0 @ X18 @ X19))),
% 1.15/1.36      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.15/1.36  thf('88', plain,
% 1.15/1.36      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 1.15/1.36         = (k2_xboole_0 @ sk_B @ 
% 1.15/1.36            (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.15/1.36      inference('sup+', [status(thm)], ['86', '87'])).
% 1.15/1.36  thf('89', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 1.15/1.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.15/1.36  thf(t3_subset, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.15/1.36  thf('90', plain,
% 1.15/1.36      (![X41 : $i, X43 : $i]:
% 1.15/1.36         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X43)) | ~ (r1_tarski @ X41 @ X43))),
% 1.15/1.36      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.36  thf('91', plain,
% 1.15/1.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['89', '90'])).
% 1.15/1.36  thf(dt_k2_subset_1, axiom,
% 1.15/1.36    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.15/1.36  thf('92', plain,
% 1.15/1.36      (![X26 : $i]: (m1_subset_1 @ (k2_subset_1 @ X26) @ (k1_zfmisc_1 @ X26))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.15/1.36  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.15/1.36  thf('93', plain, (![X23 : $i]: ((k2_subset_1 @ X23) = (X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.15/1.36  thf('94', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 1.15/1.36      inference('demod', [status(thm)], ['92', '93'])).
% 1.15/1.36  thf('95', plain,
% 1.15/1.36      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 1.15/1.36          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 1.15/1.36          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.15/1.36  thf('96', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 1.15/1.36          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['94', '95'])).
% 1.15/1.36  thf('97', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 1.15/1.36           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['91', '96'])).
% 1.15/1.36  thf('98', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.36      inference('demod', [status(thm)], ['71', '78', '83'])).
% 1.15/1.36  thf('99', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 1.15/1.36      inference('demod', [status(thm)], ['92', '93'])).
% 1.15/1.36  thf(t25_subset_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.36       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.15/1.36         ( k2_subset_1 @ A ) ) ))).
% 1.15/1.36  thf('100', plain,
% 1.15/1.36      (![X37 : $i, X38 : $i]:
% 1.15/1.36         (((k4_subset_1 @ X37 @ X38 @ (k3_subset_1 @ X37 @ X38))
% 1.15/1.36            = (k2_subset_1 @ X37))
% 1.15/1.36          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.15/1.36      inference('cnf', [status(esa)], [t25_subset_1])).
% 1.15/1.36  thf('101', plain, (![X23 : $i]: ((k2_subset_1 @ X23) = (X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.15/1.36  thf('102', plain,
% 1.15/1.36      (![X37 : $i, X38 : $i]:
% 1.15/1.36         (((k4_subset_1 @ X37 @ X38 @ (k3_subset_1 @ X37 @ X38)) = (X37))
% 1.15/1.36          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.15/1.36      inference('demod', [status(thm)], ['100', '101'])).
% 1.15/1.36  thf('103', plain,
% 1.15/1.36      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['99', '102'])).
% 1.15/1.36  thf('104', plain,
% 1.15/1.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['76', '77'])).
% 1.15/1.36  thf('105', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 1.15/1.36      inference('demod', [status(thm)], ['92', '93'])).
% 1.15/1.36  thf(d5_subset_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.36       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.15/1.36  thf('106', plain,
% 1.15/1.36      (![X24 : $i, X25 : $i]:
% 1.15/1.36         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 1.15/1.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.15/1.36      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.15/1.36  thf('107', plain,
% 1.15/1.36      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['105', '106'])).
% 1.15/1.36  thf('108', plain,
% 1.15/1.36      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['104', '107'])).
% 1.15/1.36  thf('109', plain,
% 1.15/1.36      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['103', '108'])).
% 1.15/1.36  thf('110', plain,
% 1.15/1.36      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['98', '109'])).
% 1.15/1.36  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['97', '110'])).
% 1.15/1.36  thf('112', plain,
% 1.15/1.36      (((sk_B)
% 1.15/1.36         = (k2_xboole_0 @ sk_B @ 
% 1.15/1.36            (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.15/1.36      inference('demod', [status(thm)], ['88', '111'])).
% 1.15/1.36  thf('113', plain,
% 1.15/1.36      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.15/1.36         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('sup+', [status(thm)], ['58', '112'])).
% 1.15/1.36  thf('114', plain,
% 1.15/1.36      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 1.15/1.36         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('sup+', [status(thm)], ['45', '113'])).
% 1.15/1.36  thf('115', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(t52_pre_topc, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( l1_pre_topc @ A ) =>
% 1.15/1.36       ( ![B:$i]:
% 1.15/1.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.36           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.15/1.36             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.15/1.36               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.15/1.36  thf('116', plain,
% 1.15/1.36      (![X44 : $i, X45 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.15/1.36          | ~ (v2_pre_topc @ X45)
% 1.15/1.36          | ((k2_pre_topc @ X45 @ X44) != (X44))
% 1.15/1.36          | (v4_pre_topc @ X44 @ X45)
% 1.15/1.36          | ~ (l1_pre_topc @ X45))),
% 1.15/1.36      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.15/1.36  thf('117', plain,
% 1.15/1.36      ((~ (l1_pre_topc @ sk_A)
% 1.15/1.36        | (v4_pre_topc @ sk_B @ sk_A)
% 1.15/1.36        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.15/1.36        | ~ (v2_pre_topc @ sk_A))),
% 1.15/1.36      inference('sup-', [status(thm)], ['115', '116'])).
% 1.15/1.36  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('120', plain,
% 1.15/1.36      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.15/1.36      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.15/1.36  thf('121', plain,
% 1.15/1.36      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.15/1.36         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['114', '120'])).
% 1.15/1.36  thf('122', plain,
% 1.15/1.36      (((v4_pre_topc @ sk_B @ sk_A))
% 1.15/1.36         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.15/1.36      inference('simplify', [status(thm)], ['121'])).
% 1.15/1.36  thf('123', plain,
% 1.15/1.36      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.15/1.36      inference('split', [status(esa)], ['0'])).
% 1.15/1.36  thf('124', plain,
% 1.15/1.36      (~
% 1.15/1.36       (((k2_tops_1 @ sk_A @ sk_B)
% 1.15/1.36          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.15/1.36             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.15/1.36       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.15/1.36      inference('sup-', [status(thm)], ['122', '123'])).
% 1.15/1.36  thf('125', plain, ($false),
% 1.15/1.36      inference('sat_resolution*', [status(thm)], ['1', '29', '30', '124'])).
% 1.15/1.36  
% 1.15/1.36  % SZS output end Refutation
% 1.15/1.36  
% 1.15/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
