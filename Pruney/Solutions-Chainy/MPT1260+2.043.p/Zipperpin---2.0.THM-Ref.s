%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uwRoahxycK

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:29 EST 2020

% Result     : Theorem 42.85s
% Output     : Refutation 42.85s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 840 expanded)
%              Number of leaves         :   47 ( 273 expanded)
%              Depth                    :   18
%              Number of atoms          : 2012 (8970 expanded)
%              Number of equality atoms :  140 ( 599 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('9',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( v3_pre_topc @ X58 @ X59 )
      | ~ ( r1_tarski @ X58 @ X60 )
      | ( r1_tarski @ X58 @ ( k1_tops_1 @ X59 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('30',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('43',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','28','40','41','42','43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','45'])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( ( k1_tops_1 @ X66 @ X65 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X66 ) @ X65 @ ( k2_tops_1 @ X66 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('61',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('68',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k2_tops_1 @ X57 @ X56 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k2_pre_topc @ X57 @ X56 ) @ ( k1_tops_1 @ X57 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('73',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('75',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('76',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('77',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('78',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['66','78'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('85',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X52 @ X53 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('91',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('92',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('93',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r1_tarski @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('96',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('98',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['94','102'])).

thf('104',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('107',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('108',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r1_tarski @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('115',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['106','115'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('117',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X39 @ X38 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','118'])).

thf('120',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('121',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('124',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k2_pre_topc @ X64 @ X63 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','122','127','128'])).

thf('130',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('133',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('134',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('136',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('144',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('149',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('150',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','147','152','153'])).

thf('155',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('158',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('164',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['156','165'])).

thf('167',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['133','166'])).

thf('168',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('169',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('171',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X54 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('172',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['169','175'])).

thf('177',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('178',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','82','83','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uwRoahxycK
% 0.15/0.37  % Computer   : n004.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 16:21:54 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 42.85/43.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 42.85/43.04  % Solved by: fo/fo7.sh
% 42.85/43.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.85/43.04  % done 62235 iterations in 42.537s
% 42.85/43.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 42.85/43.04  % SZS output start Refutation
% 42.85/43.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 42.85/43.04  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 42.85/43.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 42.85/43.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 42.85/43.04  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 42.85/43.04  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 42.85/43.04  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 42.85/43.04  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 42.85/43.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 42.85/43.04  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 42.85/43.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 42.85/43.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 42.85/43.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 42.85/43.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 42.85/43.04  thf(sk_A_type, type, sk_A: $i).
% 42.85/43.04  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 42.85/43.04  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 42.85/43.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 42.85/43.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 42.85/43.04  thf(sk_B_type, type, sk_B: $i).
% 42.85/43.04  thf(t76_tops_1, conjecture,
% 42.85/43.04    (![A:$i]:
% 42.85/43.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 42.85/43.04       ( ![B:$i]:
% 42.85/43.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 42.85/43.04           ( ( v3_pre_topc @ B @ A ) <=>
% 42.85/43.04             ( ( k2_tops_1 @ A @ B ) =
% 42.85/43.04               ( k7_subset_1 @
% 42.85/43.04                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 42.85/43.04  thf(zf_stmt_0, negated_conjecture,
% 42.85/43.04    (~( ![A:$i]:
% 42.85/43.04        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 42.85/43.04          ( ![B:$i]:
% 42.85/43.04            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 42.85/43.04              ( ( v3_pre_topc @ B @ A ) <=>
% 42.85/43.04                ( ( k2_tops_1 @ A @ B ) =
% 42.85/43.04                  ( k7_subset_1 @
% 42.85/43.04                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 42.85/43.04    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 42.85/43.04  thf('0', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 42.85/43.04        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('1', plain,
% 42.85/43.04      (~
% 42.85/43.04       (((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 42.85/43.04       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 42.85/43.04      inference('split', [status(esa)], ['0'])).
% 42.85/43.04  thf('2', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('3', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 42.85/43.04        | (v3_pre_topc @ sk_B @ sk_A))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('4', plain,
% 42.85/43.04      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('split', [status(esa)], ['3'])).
% 42.85/43.04  thf('5', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf(d5_subset_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.85/43.04       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 42.85/43.04  thf('6', plain,
% 42.85/43.04      (![X34 : $i, X35 : $i]:
% 42.85/43.04         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 42.85/43.04          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 42.85/43.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 42.85/43.04  thf('7', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup-', [status(thm)], ['5', '6'])).
% 42.85/43.04  thf(t36_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 42.85/43.04  thf('8', plain,
% 42.85/43.04      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 42.85/43.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 42.85/43.04  thf('9', plain,
% 42.85/43.04      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 42.85/43.04        (u1_struct_0 @ sk_A))),
% 42.85/43.04      inference('sup+', [status(thm)], ['7', '8'])).
% 42.85/43.04  thf(t3_subset, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 42.85/43.04  thf('10', plain,
% 42.85/43.04      (![X49 : $i, X51 : $i]:
% 42.85/43.04         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 42.85/43.04      inference('cnf', [status(esa)], [t3_subset])).
% 42.85/43.04  thf('11', plain,
% 42.85/43.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 42.85/43.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['9', '10'])).
% 42.85/43.04  thf(dt_k3_subset_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.85/43.04       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 42.85/43.04  thf('12', plain,
% 42.85/43.04      (![X36 : $i, X37 : $i]:
% 42.85/43.04         ((m1_subset_1 @ (k3_subset_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36))
% 42.85/43.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 42.85/43.04      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 42.85/43.04  thf('13', plain,
% 42.85/43.04      ((m1_subset_1 @ 
% 42.85/43.04        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['11', '12'])).
% 42.85/43.04  thf(t56_tops_1, axiom,
% 42.85/43.04    (![A:$i]:
% 42.85/43.04     ( ( l1_pre_topc @ A ) =>
% 42.85/43.04       ( ![B:$i]:
% 42.85/43.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 42.85/43.04           ( ![C:$i]:
% 42.85/43.04             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 42.85/43.04               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 42.85/43.04                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 42.85/43.04  thf('14', plain,
% 42.85/43.04      (![X58 : $i, X59 : $i, X60 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 42.85/43.04          | ~ (v3_pre_topc @ X58 @ X59)
% 42.85/43.04          | ~ (r1_tarski @ X58 @ X60)
% 42.85/43.04          | (r1_tarski @ X58 @ (k1_tops_1 @ X59 @ X60))
% 42.85/43.04          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 42.85/43.04          | ~ (l1_pre_topc @ X59))),
% 42.85/43.04      inference('cnf', [status(esa)], [t56_tops_1])).
% 42.85/43.04  thf('15', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (~ (l1_pre_topc @ sk_A)
% 42.85/43.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 42.85/43.04          | (r1_tarski @ 
% 42.85/43.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04             (k1_tops_1 @ sk_A @ X0))
% 42.85/43.04          | ~ (r1_tarski @ 
% 42.85/43.04               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04               X0)
% 42.85/43.04          | ~ (v3_pre_topc @ 
% 42.85/43.04               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04               sk_A))),
% 42.85/43.04      inference('sup-', [status(thm)], ['13', '14'])).
% 42.85/43.04  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('17', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 42.85/43.04          | (r1_tarski @ 
% 42.85/43.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04             (k1_tops_1 @ sk_A @ X0))
% 42.85/43.04          | ~ (r1_tarski @ 
% 42.85/43.04               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04               X0)
% 42.85/43.04          | ~ (v3_pre_topc @ 
% 42.85/43.04               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04               sk_A))),
% 42.85/43.04      inference('demod', [status(thm)], ['15', '16'])).
% 42.85/43.04  thf('18', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('19', plain,
% 42.85/43.04      (![X49 : $i, X50 : $i]:
% 42.85/43.04         ((r1_tarski @ X49 @ X50) | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 42.85/43.04      inference('cnf', [status(esa)], [t3_subset])).
% 42.85/43.04  thf('20', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 42.85/43.04      inference('sup-', [status(thm)], ['18', '19'])).
% 42.85/43.04  thf(t28_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 42.85/43.04  thf('21', plain,
% 42.85/43.04      (![X18 : $i, X19 : $i]:
% 42.85/43.04         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 42.85/43.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 42.85/43.04  thf('22', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 42.85/43.04      inference('sup-', [status(thm)], ['20', '21'])).
% 42.85/43.04  thf(commutativity_k3_xboole_0, axiom,
% 42.85/43.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 42.85/43.04  thf('23', plain,
% 42.85/43.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.85/43.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.85/43.04  thf(t100_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 42.85/43.04  thf('24', plain,
% 42.85/43.04      (![X10 : $i, X11 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X10 @ X11)
% 42.85/43.04           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 42.85/43.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 42.85/43.04  thf('25', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X0 @ X1)
% 42.85/43.04           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 42.85/43.04      inference('sup+', [status(thm)], ['23', '24'])).
% 42.85/43.04  thf('26', plain,
% 42.85/43.04      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['22', '25'])).
% 42.85/43.04  thf('27', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup-', [status(thm)], ['5', '6'])).
% 42.85/43.04  thf('28', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['26', '27'])).
% 42.85/43.04  thf('29', plain,
% 42.85/43.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 42.85/43.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['9', '10'])).
% 42.85/43.04  thf('30', plain,
% 42.85/43.04      (![X34 : $i, X35 : $i]:
% 42.85/43.04         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 42.85/43.04          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 42.85/43.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 42.85/43.04  thf('31', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 42.85/43.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['29', '30'])).
% 42.85/43.04  thf('32', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup-', [status(thm)], ['5', '6'])).
% 42.85/43.04  thf(t48_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 42.85/43.04  thf('33', plain,
% 42.85/43.04      (![X32 : $i, X33 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 42.85/43.04           = (k3_xboole_0 @ X32 @ X33))),
% 42.85/43.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 42.85/43.04  thf('34', plain,
% 42.85/43.04      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 42.85/43.04         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['32', '33'])).
% 42.85/43.04  thf('35', plain,
% 42.85/43.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.85/43.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.85/43.04  thf('36', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 42.85/43.04      inference('sup-', [status(thm)], ['20', '21'])).
% 42.85/43.04  thf('37', plain,
% 42.85/43.04      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('demod', [status(thm)], ['34', '35', '36'])).
% 42.85/43.04  thf('38', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['31', '37'])).
% 42.85/43.04  thf('39', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['26', '27'])).
% 42.85/43.04  thf('40', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('demod', [status(thm)], ['38', '39'])).
% 42.85/43.04  thf('41', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['26', '27'])).
% 42.85/43.04  thf('42', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('demod', [status(thm)], ['38', '39'])).
% 42.85/43.04  thf('43', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['26', '27'])).
% 42.85/43.04  thf('44', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('demod', [status(thm)], ['38', '39'])).
% 42.85/43.04  thf('45', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 42.85/43.04          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 42.85/43.04          | ~ (r1_tarski @ sk_B @ X0)
% 42.85/43.04          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 42.85/43.04      inference('demod', [status(thm)],
% 42.85/43.04                ['17', '28', '40', '41', '42', '43', '44'])).
% 42.85/43.04  thf('46', plain,
% 42.85/43.04      ((![X0 : $i]:
% 42.85/43.04          (~ (r1_tarski @ sk_B @ X0)
% 42.85/43.04           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 42.85/43.04           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 42.85/43.04         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['4', '45'])).
% 42.85/43.04  thf('47', plain,
% 42.85/43.04      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 42.85/43.04         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['2', '46'])).
% 42.85/43.04  thf(d10_xboole_0, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 42.85/43.04  thf('48', plain,
% 42.85/43.04      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 42.85/43.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 42.85/43.04  thf('49', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 42.85/43.04      inference('simplify', [status(thm)], ['48'])).
% 42.85/43.04  thf('50', plain,
% 42.85/43.04      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 42.85/43.04         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('demod', [status(thm)], ['47', '49'])).
% 42.85/43.04  thf('51', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf(t74_tops_1, axiom,
% 42.85/43.04    (![A:$i]:
% 42.85/43.04     ( ( l1_pre_topc @ A ) =>
% 42.85/43.04       ( ![B:$i]:
% 42.85/43.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 42.85/43.04           ( ( k1_tops_1 @ A @ B ) =
% 42.85/43.04             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 42.85/43.04  thf('52', plain,
% 42.85/43.04      (![X65 : $i, X66 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 42.85/43.04          | ((k1_tops_1 @ X66 @ X65)
% 42.85/43.04              = (k7_subset_1 @ (u1_struct_0 @ X66) @ X65 @ 
% 42.85/43.04                 (k2_tops_1 @ X66 @ X65)))
% 42.85/43.04          | ~ (l1_pre_topc @ X66))),
% 42.85/43.04      inference('cnf', [status(esa)], [t74_tops_1])).
% 42.85/43.04  thf('53', plain,
% 42.85/43.04      ((~ (l1_pre_topc @ sk_A)
% 42.85/43.04        | ((k1_tops_1 @ sk_A @ sk_B)
% 42.85/43.04            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 42.85/43.04               (k2_tops_1 @ sk_A @ sk_B))))),
% 42.85/43.04      inference('sup-', [status(thm)], ['51', '52'])).
% 42.85/43.04  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('55', plain,
% 42.85/43.04      (((k1_tops_1 @ sk_A @ sk_B)
% 42.85/43.04         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 42.85/43.04            (k2_tops_1 @ sk_A @ sk_B)))),
% 42.85/43.04      inference('demod', [status(thm)], ['53', '54'])).
% 42.85/43.04  thf('56', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf(redefinition_k7_subset_1, axiom,
% 42.85/43.04    (![A:$i,B:$i,C:$i]:
% 42.85/43.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.85/43.04       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 42.85/43.04  thf('57', plain,
% 42.85/43.04      (![X44 : $i, X45 : $i, X46 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 42.85/43.04          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 42.85/43.04      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 42.85/43.04  thf('58', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 42.85/43.04           = (k4_xboole_0 @ sk_B @ X0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['56', '57'])).
% 42.85/43.04  thf('59', plain,
% 42.85/43.04      (((k1_tops_1 @ sk_A @ sk_B)
% 42.85/43.04         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 42.85/43.04      inference('demod', [status(thm)], ['55', '58'])).
% 42.85/43.04  thf('60', plain,
% 42.85/43.04      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 42.85/43.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 42.85/43.04  thf('61', plain,
% 42.85/43.04      (![X4 : $i, X6 : $i]:
% 42.85/43.04         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 42.85/43.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 42.85/43.04  thf('62', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 42.85/43.04          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['60', '61'])).
% 42.85/43.04  thf('63', plain,
% 42.85/43.04      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 42.85/43.04        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 42.85/43.04      inference('sup-', [status(thm)], ['59', '62'])).
% 42.85/43.04  thf('64', plain,
% 42.85/43.04      (((k1_tops_1 @ sk_A @ sk_B)
% 42.85/43.04         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 42.85/43.04      inference('demod', [status(thm)], ['55', '58'])).
% 42.85/43.04  thf('65', plain,
% 42.85/43.04      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 42.85/43.04        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 42.85/43.04      inference('demod', [status(thm)], ['63', '64'])).
% 42.85/43.04  thf('66', plain,
% 42.85/43.04      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 42.85/43.04         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['50', '65'])).
% 42.85/43.04  thf('67', plain,
% 42.85/43.04      ((m1_subset_1 @ 
% 42.85/43.04        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 42.85/43.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['11', '12'])).
% 42.85/43.04  thf(l78_tops_1, axiom,
% 42.85/43.04    (![A:$i]:
% 42.85/43.04     ( ( l1_pre_topc @ A ) =>
% 42.85/43.04       ( ![B:$i]:
% 42.85/43.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 42.85/43.04           ( ( k2_tops_1 @ A @ B ) =
% 42.85/43.04             ( k7_subset_1 @
% 42.85/43.04               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 42.85/43.04               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 42.85/43.04  thf('68', plain,
% 42.85/43.04      (![X56 : $i, X57 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 42.85/43.04          | ((k2_tops_1 @ X57 @ X56)
% 42.85/43.04              = (k7_subset_1 @ (u1_struct_0 @ X57) @ 
% 42.85/43.04                 (k2_pre_topc @ X57 @ X56) @ (k1_tops_1 @ X57 @ X56)))
% 42.85/43.04          | ~ (l1_pre_topc @ X57))),
% 42.85/43.04      inference('cnf', [status(esa)], [l78_tops_1])).
% 42.85/43.04  thf('69', plain,
% 42.85/43.04      ((~ (l1_pre_topc @ sk_A)
% 42.85/43.04        | ((k2_tops_1 @ sk_A @ 
% 42.85/43.04            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 42.85/43.04            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04               (k2_pre_topc @ sk_A @ 
% 42.85/43.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 42.85/43.04               (k1_tops_1 @ sk_A @ 
% 42.85/43.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 42.85/43.04      inference('sup-', [status(thm)], ['67', '68'])).
% 42.85/43.04  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('71', plain,
% 42.85/43.04      (((k2_tops_1 @ sk_A @ 
% 42.85/43.04         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 42.85/43.04         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04            (k2_pre_topc @ sk_A @ 
% 42.85/43.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 42.85/43.04            (k1_tops_1 @ sk_A @ 
% 42.85/43.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 42.85/43.04      inference('demod', [status(thm)], ['69', '70'])).
% 42.85/43.04  thf('72', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['26', '27'])).
% 42.85/43.04  thf('73', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('demod', [status(thm)], ['38', '39'])).
% 42.85/43.04  thf('74', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['26', '27'])).
% 42.85/43.04  thf('75', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('demod', [status(thm)], ['38', '39'])).
% 42.85/43.04  thf('76', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 42.85/43.04         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 42.85/43.04      inference('sup+', [status(thm)], ['26', '27'])).
% 42.85/43.04  thf('77', plain,
% 42.85/43.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 42.85/43.04      inference('demod', [status(thm)], ['38', '39'])).
% 42.85/43.04  thf('78', plain,
% 42.85/43.04      (((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 42.85/43.04            (k1_tops_1 @ sk_A @ sk_B)))),
% 42.85/43.04      inference('demod', [status(thm)],
% 42.85/43.04                ['71', '72', '73', '74', '75', '76', '77'])).
% 42.85/43.04  thf('79', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 42.85/43.04         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('sup+', [status(thm)], ['66', '78'])).
% 42.85/43.04  thf('80', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 42.85/43.04         <= (~
% 42.85/43.04             (((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 42.85/43.04      inference('split', [status(esa)], ['0'])).
% 42.85/43.04  thf('81', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 42.85/43.04         <= (~
% 42.85/43.04             (((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 42.85/43.04             ((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['79', '80'])).
% 42.85/43.04  thf('82', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 42.85/43.04       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 42.85/43.04      inference('simplify', [status(thm)], ['81'])).
% 42.85/43.04  thf('83', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 42.85/43.04       ((v3_pre_topc @ sk_B @ sk_A))),
% 42.85/43.04      inference('split', [status(esa)], ['3'])).
% 42.85/43.04  thf('84', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf(dt_k2_tops_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( ( l1_pre_topc @ A ) & 
% 42.85/43.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 42.85/43.04       ( m1_subset_1 @
% 42.85/43.04         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 42.85/43.04  thf('85', plain,
% 42.85/43.04      (![X52 : $i, X53 : $i]:
% 42.85/43.04         (~ (l1_pre_topc @ X52)
% 42.85/43.04          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 42.85/43.04          | (m1_subset_1 @ (k2_tops_1 @ X52 @ X53) @ 
% 42.85/43.04             (k1_zfmisc_1 @ (u1_struct_0 @ X52))))),
% 42.85/43.04      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 42.85/43.04  thf('86', plain,
% 42.85/43.04      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 42.85/43.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 42.85/43.04        | ~ (l1_pre_topc @ sk_A))),
% 42.85/43.04      inference('sup-', [status(thm)], ['84', '85'])).
% 42.85/43.04  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('88', plain,
% 42.85/43.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 42.85/43.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('demod', [status(thm)], ['86', '87'])).
% 42.85/43.04  thf('89', plain,
% 42.85/43.04      (![X49 : $i, X50 : $i]:
% 42.85/43.04         ((r1_tarski @ X49 @ X50) | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 42.85/43.04      inference('cnf', [status(esa)], [t3_subset])).
% 42.85/43.04  thf('90', plain,
% 42.85/43.04      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 42.85/43.04      inference('sup-', [status(thm)], ['88', '89'])).
% 42.85/43.04  thf(l32_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 42.85/43.04  thf('91', plain,
% 42.85/43.04      (![X7 : $i, X9 : $i]:
% 42.85/43.04         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 42.85/43.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 42.85/43.04  thf('92', plain,
% 42.85/43.04      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 42.85/43.04         = (k1_xboole_0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['90', '91'])).
% 42.85/43.04  thf(t44_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i,C:$i]:
% 42.85/43.04     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 42.85/43.04       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 42.85/43.04  thf('93', plain,
% 42.85/43.04      (![X27 : $i, X28 : $i, X29 : $i]:
% 42.85/43.04         ((r1_tarski @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 42.85/43.04          | ~ (r1_tarski @ (k4_xboole_0 @ X27 @ X28) @ X29))),
% 42.85/43.04      inference('cnf', [status(esa)], [t44_xboole_1])).
% 42.85/43.04  thf('94', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 42.85/43.04          | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 42.85/43.04             (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['92', '93'])).
% 42.85/43.04  thf(commutativity_k2_xboole_0, axiom,
% 42.85/43.04    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 42.85/43.04  thf('95', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.85/43.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.85/43.04  thf(t1_boole, axiom,
% 42.85/43.04    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 42.85/43.04  thf('96', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 42.85/43.04      inference('cnf', [status(esa)], [t1_boole])).
% 42.85/43.04  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['95', '96'])).
% 42.85/43.04  thf(t46_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 42.85/43.04  thf('98', plain,
% 42.85/43.04      (![X30 : $i, X31 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 42.85/43.04      inference('cnf', [status(esa)], [t46_xboole_1])).
% 42.85/43.04  thf('99', plain,
% 42.85/43.04      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['97', '98'])).
% 42.85/43.04  thf('100', plain,
% 42.85/43.04      (![X7 : $i, X8 : $i]:
% 42.85/43.04         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 42.85/43.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 42.85/43.04  thf('101', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['99', '100'])).
% 42.85/43.04  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 42.85/43.04      inference('simplify', [status(thm)], ['101'])).
% 42.85/43.04  thf('103', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 42.85/43.04          (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 42.85/43.04      inference('demod', [status(thm)], ['94', '102'])).
% 42.85/43.04  thf('104', plain,
% 42.85/43.04      (![X49 : $i, X51 : $i]:
% 42.85/43.04         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 42.85/43.04      inference('cnf', [status(esa)], [t3_subset])).
% 42.85/43.04  thf('105', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 42.85/43.04          (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['103', '104'])).
% 42.85/43.04  thf('106', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.85/43.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.85/43.04  thf('107', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 42.85/43.04      inference('sup-', [status(thm)], ['18', '19'])).
% 42.85/43.04  thf('108', plain,
% 42.85/43.04      (![X7 : $i, X9 : $i]:
% 42.85/43.04         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 42.85/43.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 42.85/43.04  thf('109', plain,
% 42.85/43.04      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['107', '108'])).
% 42.85/43.04  thf('110', plain,
% 42.85/43.04      (![X27 : $i, X28 : $i, X29 : $i]:
% 42.85/43.04         ((r1_tarski @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 42.85/43.04          | ~ (r1_tarski @ (k4_xboole_0 @ X27 @ X28) @ X29))),
% 42.85/43.04      inference('cnf', [status(esa)], [t44_xboole_1])).
% 42.85/43.04  thf('111', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 42.85/43.04          | (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['109', '110'])).
% 42.85/43.04  thf('112', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 42.85/43.04      inference('simplify', [status(thm)], ['101'])).
% 42.85/43.04  thf('113', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 42.85/43.04      inference('demod', [status(thm)], ['111', '112'])).
% 42.85/43.04  thf('114', plain,
% 42.85/43.04      (![X49 : $i, X51 : $i]:
% 42.85/43.04         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 42.85/43.04      inference('cnf', [status(esa)], [t3_subset])).
% 42.85/43.04  thf('115', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (m1_subset_1 @ sk_B @ 
% 42.85/43.04          (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 42.85/43.04      inference('sup-', [status(thm)], ['113', '114'])).
% 42.85/43.04  thf('116', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         (m1_subset_1 @ sk_B @ 
% 42.85/43.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 42.85/43.04      inference('sup+', [status(thm)], ['106', '115'])).
% 42.85/43.04  thf(dt_k4_subset_1, axiom,
% 42.85/43.04    (![A:$i,B:$i,C:$i]:
% 42.85/43.04     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 42.85/43.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 42.85/43.04       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 42.85/43.04  thf('117', plain,
% 42.85/43.04      (![X38 : $i, X39 : $i, X40 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 42.85/43.04          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 42.85/43.04          | (m1_subset_1 @ (k4_subset_1 @ X39 @ X38 @ X40) @ 
% 42.85/43.04             (k1_zfmisc_1 @ X39)))),
% 42.85/43.04      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 42.85/43.04  thf('118', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((m1_subset_1 @ 
% 42.85/43.04           (k4_subset_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B @ X1) @ 
% 42.85/43.04           (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))
% 42.85/43.04          | ~ (m1_subset_1 @ X1 @ 
% 42.85/43.04               (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 42.85/43.04      inference('sup-', [status(thm)], ['116', '117'])).
% 42.85/43.04  thf('119', plain,
% 42.85/43.04      ((m1_subset_1 @ 
% 42.85/43.04        (k4_subset_1 @ 
% 42.85/43.04         (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 42.85/43.04         (k2_tops_1 @ sk_A @ sk_B)) @ 
% 42.85/43.04        (k1_zfmisc_1 @ 
% 42.85/43.04         (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 42.85/43.04      inference('sup-', [status(thm)], ['105', '118'])).
% 42.85/43.04  thf('120', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 42.85/43.04      inference('simplify', [status(thm)], ['48'])).
% 42.85/43.04  thf(t12_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 42.85/43.04  thf('121', plain,
% 42.85/43.04      (![X12 : $i, X13 : $i]:
% 42.85/43.04         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 42.85/43.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 42.85/43.04  thf('122', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['120', '121'])).
% 42.85/43.04  thf('123', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf(t65_tops_1, axiom,
% 42.85/43.04    (![A:$i]:
% 42.85/43.04     ( ( l1_pre_topc @ A ) =>
% 42.85/43.04       ( ![B:$i]:
% 42.85/43.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 42.85/43.04           ( ( k2_pre_topc @ A @ B ) =
% 42.85/43.04             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 42.85/43.04  thf('124', plain,
% 42.85/43.04      (![X63 : $i, X64 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 42.85/43.04          | ((k2_pre_topc @ X64 @ X63)
% 42.85/43.04              = (k4_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 42.85/43.04                 (k2_tops_1 @ X64 @ X63)))
% 42.85/43.04          | ~ (l1_pre_topc @ X64))),
% 42.85/43.04      inference('cnf', [status(esa)], [t65_tops_1])).
% 42.85/43.04  thf('125', plain,
% 42.85/43.04      ((~ (l1_pre_topc @ sk_A)
% 42.85/43.04        | ((k2_pre_topc @ sk_A @ sk_B)
% 42.85/43.04            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 42.85/43.04               (k2_tops_1 @ sk_A @ sk_B))))),
% 42.85/43.04      inference('sup-', [status(thm)], ['123', '124'])).
% 42.85/43.04  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('127', plain,
% 42.85/43.04      (((k2_pre_topc @ sk_A @ sk_B)
% 42.85/43.04         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 42.85/43.04            (k2_tops_1 @ sk_A @ sk_B)))),
% 42.85/43.04      inference('demod', [status(thm)], ['125', '126'])).
% 42.85/43.04  thf('128', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['120', '121'])).
% 42.85/43.04  thf('129', plain,
% 42.85/43.04      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 42.85/43.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('demod', [status(thm)], ['119', '122', '127', '128'])).
% 42.85/43.04  thf('130', plain,
% 42.85/43.04      (![X44 : $i, X45 : $i, X46 : $i]:
% 42.85/43.04         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 42.85/43.04          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 42.85/43.04      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 42.85/43.04  thf('131', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 42.85/43.04           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['129', '130'])).
% 42.85/43.04  thf('132', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 42.85/43.04         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 42.85/43.04      inference('split', [status(esa)], ['3'])).
% 42.85/43.04  thf('133', plain,
% 42.85/43.04      ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 42.85/43.04         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 42.85/43.04      inference('sup+', [status(thm)], ['131', '132'])).
% 42.85/43.04  thf(t39_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 42.85/43.04  thf('134', plain,
% 42.85/43.04      (![X22 : $i, X23 : $i]:
% 42.85/43.04         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 42.85/43.04           = (k2_xboole_0 @ X22 @ X23))),
% 42.85/43.04      inference('cnf', [status(esa)], [t39_xboole_1])).
% 42.85/43.04  thf('135', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.85/43.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.85/43.04  thf(t40_xboole_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 42.85/43.04  thf('136', plain,
% 42.85/43.04      (![X25 : $i, X26 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26)
% 42.85/43.04           = (k4_xboole_0 @ X25 @ X26))),
% 42.85/43.04      inference('cnf', [status(esa)], [t40_xboole_1])).
% 42.85/43.04  thf('137', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 42.85/43.04           = (k4_xboole_0 @ X0 @ X1))),
% 42.85/43.04      inference('sup+', [status(thm)], ['135', '136'])).
% 42.85/43.04  thf('138', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 42.85/43.04           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 42.85/43.04      inference('sup+', [status(thm)], ['134', '137'])).
% 42.85/43.04  thf('139', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 42.85/43.04           = (k4_xboole_0 @ X0 @ X1))),
% 42.85/43.04      inference('sup+', [status(thm)], ['135', '136'])).
% 42.85/43.04  thf('140', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X0 @ X1)
% 42.85/43.04           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 42.85/43.04      inference('demod', [status(thm)], ['138', '139'])).
% 42.85/43.04  thf('141', plain,
% 42.85/43.04      (![X32 : $i, X33 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 42.85/43.04           = (k3_xboole_0 @ X32 @ X33))),
% 42.85/43.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 42.85/43.04  thf('142', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 42.85/43.04           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['140', '141'])).
% 42.85/43.04  thf('143', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 42.85/43.04      inference('simplify', [status(thm)], ['48'])).
% 42.85/43.04  thf('144', plain,
% 42.85/43.04      (![X18 : $i, X19 : $i]:
% 42.85/43.04         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 42.85/43.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 42.85/43.04  thf('145', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['143', '144'])).
% 42.85/43.04  thf('146', plain,
% 42.85/43.04      (![X10 : $i, X11 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X10 @ X11)
% 42.85/43.04           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 42.85/43.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 42.85/43.04  thf('147', plain,
% 42.85/43.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['145', '146'])).
% 42.85/43.04  thf('148', plain,
% 42.85/43.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['145', '146'])).
% 42.85/43.04  thf('149', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 42.85/43.04      inference('cnf', [status(esa)], [t1_boole])).
% 42.85/43.04  thf('150', plain,
% 42.85/43.04      (![X30 : $i, X31 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 42.85/43.04      inference('cnf', [status(esa)], [t46_xboole_1])).
% 42.85/43.04  thf('151', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['149', '150'])).
% 42.85/43.04  thf('152', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['148', '151'])).
% 42.85/43.04  thf('153', plain,
% 42.85/43.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.85/43.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.85/43.04  thf('154', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 42.85/43.04      inference('demod', [status(thm)], ['142', '147', '152', '153'])).
% 42.85/43.04  thf('155', plain,
% 42.85/43.04      (![X10 : $i, X11 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X10 @ X11)
% 42.85/43.04           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 42.85/43.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 42.85/43.04  thf('156', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 42.85/43.04           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['154', '155'])).
% 42.85/43.04  thf('157', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 42.85/43.04      inference('simplify', [status(thm)], ['101'])).
% 42.85/43.04  thf('158', plain,
% 42.85/43.04      (![X18 : $i, X19 : $i]:
% 42.85/43.04         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 42.85/43.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 42.85/43.04  thf('159', plain,
% 42.85/43.04      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 42.85/43.04      inference('sup-', [status(thm)], ['157', '158'])).
% 42.85/43.04  thf('160', plain,
% 42.85/43.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.85/43.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.85/43.04  thf('161', plain,
% 42.85/43.04      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['159', '160'])).
% 42.85/43.04  thf('162', plain,
% 42.85/43.04      (![X10 : $i, X11 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X10 @ X11)
% 42.85/43.04           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 42.85/43.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 42.85/43.04  thf('163', plain,
% 42.85/43.04      (![X0 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['161', '162'])).
% 42.85/43.04  thf(t3_boole, axiom,
% 42.85/43.04    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 42.85/43.04  thf('164', plain, (![X24 : $i]: ((k4_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 42.85/43.04      inference('cnf', [status(esa)], [t3_boole])).
% 42.85/43.04  thf('165', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 42.85/43.04      inference('sup+', [status(thm)], ['163', '164'])).
% 42.85/43.04  thf('166', plain,
% 42.85/43.04      (![X0 : $i, X1 : $i]:
% 42.85/43.04         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 42.85/43.04      inference('demod', [status(thm)], ['156', '165'])).
% 42.85/43.04  thf('167', plain,
% 42.85/43.04      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 42.85/43.04         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 42.85/43.04      inference('sup+', [status(thm)], ['133', '166'])).
% 42.85/43.04  thf('168', plain,
% 42.85/43.04      (((k1_tops_1 @ sk_A @ sk_B)
% 42.85/43.04         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 42.85/43.04      inference('demod', [status(thm)], ['55', '58'])).
% 42.85/43.04  thf('169', plain,
% 42.85/43.04      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 42.85/43.04         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 42.85/43.04      inference('sup+', [status(thm)], ['167', '168'])).
% 42.85/43.04  thf('170', plain,
% 42.85/43.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf(fc9_tops_1, axiom,
% 42.85/43.04    (![A:$i,B:$i]:
% 42.85/43.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 42.85/43.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 42.85/43.04       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 42.85/43.04  thf('171', plain,
% 42.85/43.04      (![X54 : $i, X55 : $i]:
% 42.85/43.04         (~ (l1_pre_topc @ X54)
% 42.85/43.04          | ~ (v2_pre_topc @ X54)
% 42.85/43.04          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 42.85/43.04          | (v3_pre_topc @ (k1_tops_1 @ X54 @ X55) @ X54))),
% 42.85/43.04      inference('cnf', [status(esa)], [fc9_tops_1])).
% 42.85/43.04  thf('172', plain,
% 42.85/43.04      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 42.85/43.04        | ~ (v2_pre_topc @ sk_A)
% 42.85/43.04        | ~ (l1_pre_topc @ sk_A))),
% 42.85/43.04      inference('sup-', [status(thm)], ['170', '171'])).
% 42.85/43.04  thf('173', plain, ((v2_pre_topc @ sk_A)),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 42.85/43.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.85/43.04  thf('175', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 42.85/43.04      inference('demod', [status(thm)], ['172', '173', '174'])).
% 42.85/43.04  thf('176', plain,
% 42.85/43.04      (((v3_pre_topc @ sk_B @ sk_A))
% 42.85/43.04         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 42.85/43.04      inference('sup+', [status(thm)], ['169', '175'])).
% 42.85/43.04  thf('177', plain,
% 42.85/43.04      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 42.85/43.04      inference('split', [status(esa)], ['0'])).
% 42.85/43.04  thf('178', plain,
% 42.85/43.04      (~
% 42.85/43.04       (((k2_tops_1 @ sk_A @ sk_B)
% 42.85/43.04          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 42.85/43.04             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 42.85/43.04       ((v3_pre_topc @ sk_B @ sk_A))),
% 42.85/43.04      inference('sup-', [status(thm)], ['176', '177'])).
% 42.85/43.04  thf('179', plain, ($false),
% 42.85/43.04      inference('sat_resolution*', [status(thm)], ['1', '82', '83', '178'])).
% 42.85/43.04  
% 42.85/43.04  % SZS output end Refutation
% 42.85/43.04  
% 42.85/43.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
