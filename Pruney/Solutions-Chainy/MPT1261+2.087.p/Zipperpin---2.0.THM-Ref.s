%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a6ojnEOroG

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:50 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 790 expanded)
%              Number of leaves         :   44 ( 239 expanded)
%              Depth                    :   20
%              Number of atoms          : 1567 (10167 expanded)
%              Number of equality atoms :  113 ( 609 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

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

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('4',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X62 @ X61 ) @ X61 )
      | ~ ( v4_pre_topc @ X61 @ X62 )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','26','27'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

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
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_pre_topc @ X60 @ X59 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
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

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X41 @ X43 )
        = ( k4_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X9 @ ( k2_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k2_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','62'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v2_pre_topc @ X54 )
      | ( ( k2_pre_topc @ X54 @ X53 )
       != X53 )
      | ( v4_pre_topc @ X53 @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('73',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('75',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['30','73','74'])).

thf('76',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['28','75'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k3_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('78',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('88',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k1_tops_1 @ X64 @ X63 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('93',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('95',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['86','93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('98',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('101',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['95','102'])).

thf('104',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['86','93','94'])).

thf('105',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('107',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('109',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['30','73','74'])).

thf('111',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('113',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('117',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('118',plain,
    ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['103','104','118'])).

thf('120',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('123',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X56 @ X55 ) @ X55 )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('130',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121','130'])).

thf('132',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['30','73'])).

thf('133',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a6ojnEOroG
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.28/1.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.28/1.47  % Solved by: fo/fo7.sh
% 1.28/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.47  % done 3686 iterations in 1.008s
% 1.28/1.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.28/1.47  % SZS output start Refutation
% 1.28/1.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.28/1.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.28/1.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.28/1.47  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.28/1.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.28/1.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.28/1.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.28/1.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.28/1.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.28/1.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.28/1.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.28/1.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.28/1.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.28/1.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.28/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.47  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.28/1.47  thf(sk_B_type, type, sk_B: $i).
% 1.28/1.47  thf(t7_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.28/1.47  thf('0', plain,
% 1.28/1.47      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 1.28/1.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.28/1.47  thf(t77_tops_1, conjecture,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.28/1.47       ( ![B:$i]:
% 1.28/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.28/1.47           ( ( v4_pre_topc @ B @ A ) <=>
% 1.28/1.47             ( ( k2_tops_1 @ A @ B ) =
% 1.28/1.47               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.28/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.47    (~( ![A:$i]:
% 1.28/1.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.28/1.47          ( ![B:$i]:
% 1.28/1.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.28/1.47              ( ( v4_pre_topc @ B @ A ) <=>
% 1.28/1.47                ( ( k2_tops_1 @ A @ B ) =
% 1.28/1.47                  ( k7_subset_1 @
% 1.28/1.47                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.28/1.47    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.28/1.47  thf('1', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47             (k1_tops_1 @ sk_A @ sk_B)))
% 1.28/1.47        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('2', plain,
% 1.28/1.47      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('split', [status(esa)], ['1'])).
% 1.28/1.47  thf('3', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(t69_tops_1, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( l1_pre_topc @ A ) =>
% 1.28/1.47       ( ![B:$i]:
% 1.28/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.28/1.47           ( ( v4_pre_topc @ B @ A ) =>
% 1.28/1.47             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.28/1.47  thf('4', plain,
% 1.28/1.47      (![X61 : $i, X62 : $i]:
% 1.28/1.47         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 1.28/1.47          | (r1_tarski @ (k2_tops_1 @ X62 @ X61) @ X61)
% 1.28/1.47          | ~ (v4_pre_topc @ X61 @ X62)
% 1.28/1.47          | ~ (l1_pre_topc @ X62))),
% 1.28/1.47      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.28/1.47  thf('5', plain,
% 1.28/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.28/1.47        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.28/1.47        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.28/1.47      inference('sup-', [status(thm)], ['3', '4'])).
% 1.28/1.47  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('7', plain,
% 1.28/1.47      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.28/1.47        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.28/1.47  thf('8', plain,
% 1.28/1.47      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['2', '7'])).
% 1.28/1.47  thf(t1_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.28/1.47       ( r1_tarski @ A @ C ) ))).
% 1.28/1.47  thf('9', plain,
% 1.28/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.28/1.47         (~ (r1_tarski @ X15 @ X16)
% 1.28/1.47          | ~ (r1_tarski @ X16 @ X17)
% 1.28/1.47          | (r1_tarski @ X15 @ X17))),
% 1.28/1.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.28/1.47  thf('10', plain,
% 1.28/1.47      ((![X0 : $i]:
% 1.28/1.47          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.28/1.47           | ~ (r1_tarski @ sk_B @ X0)))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['8', '9'])).
% 1.28/1.47  thf('11', plain,
% 1.28/1.47      ((![X0 : $i]:
% 1.28/1.47          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['0', '10'])).
% 1.28/1.47  thf(t43_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.28/1.47       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.28/1.47  thf('12', plain,
% 1.28/1.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.28/1.47         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 1.28/1.47          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.28/1.47      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.28/1.47  thf('13', plain,
% 1.28/1.47      ((![X0 : $i]:
% 1.28/1.47          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['11', '12'])).
% 1.28/1.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.28/1.47  thf('14', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 1.28/1.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.28/1.47  thf(d10_xboole_0, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.28/1.47  thf('15', plain,
% 1.28/1.47      (![X4 : $i, X6 : $i]:
% 1.28/1.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.28/1.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.28/1.47  thf('16', plain,
% 1.28/1.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['14', '15'])).
% 1.28/1.47  thf('17', plain,
% 1.28/1.47      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['13', '16'])).
% 1.28/1.47  thf(t48_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.28/1.47  thf('18', plain,
% 1.28/1.47      (![X28 : $i, X29 : $i]:
% 1.28/1.47         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 1.28/1.47           = (k3_xboole_0 @ X28 @ X29))),
% 1.28/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.28/1.47  thf('19', plain,
% 1.28/1.47      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.28/1.47          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup+', [status(thm)], ['17', '18'])).
% 1.28/1.47  thf(commutativity_k2_xboole_0, axiom,
% 1.28/1.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.28/1.47  thf('20', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.28/1.47  thf(t1_boole, axiom,
% 1.28/1.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.28/1.47  thf('21', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.28/1.47      inference('cnf', [status(esa)], [t1_boole])).
% 1.28/1.47  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.28/1.47      inference('sup+', [status(thm)], ['20', '21'])).
% 1.28/1.47  thf(t39_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.28/1.47  thf('23', plain,
% 1.28/1.47      (![X21 : $i, X22 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 1.28/1.47           = (k2_xboole_0 @ X21 @ X22))),
% 1.28/1.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.28/1.47  thf('24', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.28/1.47      inference('sup+', [status(thm)], ['22', '23'])).
% 1.28/1.47  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.28/1.47      inference('sup+', [status(thm)], ['20', '21'])).
% 1.28/1.47  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.28/1.47      inference('demod', [status(thm)], ['24', '25'])).
% 1.28/1.47  thf(commutativity_k3_xboole_0, axiom,
% 1.28/1.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.28/1.47  thf('27', plain,
% 1.28/1.47      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.28/1.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.28/1.47  thf('28', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('demod', [status(thm)], ['19', '26', '27'])).
% 1.28/1.47  thf('29', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47              (k1_tops_1 @ sk_A @ sk_B)))
% 1.28/1.47        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('30', plain,
% 1.28/1.47      (~
% 1.28/1.47       (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.28/1.47       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.28/1.47      inference('split', [status(esa)], ['29'])).
% 1.28/1.47  thf('31', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(t65_tops_1, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( l1_pre_topc @ A ) =>
% 1.28/1.47       ( ![B:$i]:
% 1.28/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.28/1.47           ( ( k2_pre_topc @ A @ B ) =
% 1.28/1.47             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.28/1.47  thf('32', plain,
% 1.28/1.47      (![X59 : $i, X60 : $i]:
% 1.28/1.47         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.28/1.47          | ((k2_pre_topc @ X60 @ X59)
% 1.28/1.47              = (k4_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 1.28/1.47                 (k2_tops_1 @ X60 @ X59)))
% 1.28/1.47          | ~ (l1_pre_topc @ X60))),
% 1.28/1.47      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.28/1.47  thf('33', plain,
% 1.28/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.28/1.47        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.28/1.47            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['31', '32'])).
% 1.28/1.47  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('35', plain,
% 1.28/1.47      (((k2_pre_topc @ sk_A @ sk_B)
% 1.28/1.47         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('demod', [status(thm)], ['33', '34'])).
% 1.28/1.47  thf('36', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(redefinition_k7_subset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.28/1.47       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.28/1.47  thf('37', plain,
% 1.28/1.47      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.28/1.47         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 1.28/1.47          | ((k7_subset_1 @ X42 @ X41 @ X43) = (k4_xboole_0 @ X41 @ X43)))),
% 1.28/1.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.28/1.47  thf('38', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.28/1.47           = (k4_xboole_0 @ sk_B @ X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['36', '37'])).
% 1.28/1.47  thf('39', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47             (k1_tops_1 @ sk_A @ sk_B))))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('split', [status(esa)], ['1'])).
% 1.28/1.47  thf('40', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('sup+', [status(thm)], ['38', '39'])).
% 1.28/1.47  thf('41', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(t3_subset, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.28/1.47  thf('42', plain,
% 1.28/1.47      (![X47 : $i, X48 : $i]:
% 1.28/1.47         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 1.28/1.47      inference('cnf', [status(esa)], [t3_subset])).
% 1.28/1.47  thf('43', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('sup-', [status(thm)], ['41', '42'])).
% 1.28/1.47  thf(t10_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.28/1.47  thf('44', plain,
% 1.28/1.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.28/1.47         (~ (r1_tarski @ X9 @ X10)
% 1.28/1.47          | (r1_tarski @ X9 @ (k2_xboole_0 @ X11 @ X10)))),
% 1.28/1.47      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.28/1.47  thf('45', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['43', '44'])).
% 1.28/1.47  thf('46', plain,
% 1.28/1.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.28/1.47         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 1.28/1.47          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.28/1.47      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.28/1.47  thf('47', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('sup-', [status(thm)], ['45', '46'])).
% 1.28/1.47  thf('48', plain,
% 1.28/1.47      (![X47 : $i, X49 : $i]:
% 1.28/1.47         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 1.28/1.47      inference('cnf', [status(esa)], [t3_subset])).
% 1.28/1.47  thf('49', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.28/1.47          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['47', '48'])).
% 1.28/1.47  thf('50', plain,
% 1.28/1.47      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.28/1.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('sup+', [status(thm)], ['40', '49'])).
% 1.28/1.47  thf('51', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(redefinition_k4_subset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.28/1.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.28/1.47       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.28/1.47  thf('52', plain,
% 1.28/1.47      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.28/1.47         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.28/1.47          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 1.28/1.47          | ((k4_subset_1 @ X39 @ X38 @ X40) = (k2_xboole_0 @ X38 @ X40)))),
% 1.28/1.47      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.28/1.47  thf('53', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.28/1.47            = (k2_xboole_0 @ sk_B @ X0))
% 1.28/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['51', '52'])).
% 1.28/1.47  thf('54', plain,
% 1.28/1.47      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.28/1.47          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['50', '53'])).
% 1.28/1.47  thf('55', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('sup+', [status(thm)], ['38', '39'])).
% 1.28/1.47  thf(t36_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.28/1.47  thf('56', plain,
% 1.28/1.47      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.28/1.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.28/1.47  thf(t12_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.28/1.47  thf('57', plain,
% 1.28/1.47      (![X12 : $i, X13 : $i]:
% 1.28/1.47         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.28/1.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.28/1.47  thf('58', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['56', '57'])).
% 1.28/1.47  thf('59', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.28/1.47  thf('60', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.28/1.47      inference('demod', [status(thm)], ['58', '59'])).
% 1.28/1.47  thf('61', plain,
% 1.28/1.47      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('sup+', [status(thm)], ['55', '60'])).
% 1.28/1.47  thf('62', plain,
% 1.28/1.47      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.28/1.47          = (sk_B)))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('demod', [status(thm)], ['54', '61'])).
% 1.28/1.47  thf('63', plain,
% 1.28/1.47      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('sup+', [status(thm)], ['35', '62'])).
% 1.28/1.47  thf('64', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(t52_pre_topc, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( l1_pre_topc @ A ) =>
% 1.28/1.47       ( ![B:$i]:
% 1.28/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.28/1.47           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.28/1.47             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.28/1.47               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.28/1.47  thf('65', plain,
% 1.28/1.47      (![X53 : $i, X54 : $i]:
% 1.28/1.47         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.28/1.47          | ~ (v2_pre_topc @ X54)
% 1.28/1.47          | ((k2_pre_topc @ X54 @ X53) != (X53))
% 1.28/1.47          | (v4_pre_topc @ X53 @ X54)
% 1.28/1.47          | ~ (l1_pre_topc @ X54))),
% 1.28/1.47      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.28/1.47  thf('66', plain,
% 1.28/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.28/1.47        | (v4_pre_topc @ sk_B @ sk_A)
% 1.28/1.47        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.28/1.47        | ~ (v2_pre_topc @ sk_A))),
% 1.28/1.47      inference('sup-', [status(thm)], ['64', '65'])).
% 1.28/1.47  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('69', plain,
% 1.28/1.47      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.28/1.47      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.28/1.47  thf('70', plain,
% 1.28/1.47      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['63', '69'])).
% 1.28/1.47  thf('71', plain,
% 1.28/1.47      (((v4_pre_topc @ sk_B @ sk_A))
% 1.28/1.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('simplify', [status(thm)], ['70'])).
% 1.28/1.47  thf('72', plain,
% 1.28/1.47      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('split', [status(esa)], ['29'])).
% 1.28/1.47  thf('73', plain,
% 1.28/1.47      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.28/1.47       ~
% 1.28/1.47       (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['71', '72'])).
% 1.28/1.47  thf('74', plain,
% 1.28/1.47      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.28/1.47       (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.28/1.47      inference('split', [status(esa)], ['1'])).
% 1.28/1.47  thf('75', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.28/1.47      inference('sat_resolution*', [status(thm)], ['30', '73', '74'])).
% 1.28/1.47  thf('76', plain,
% 1.28/1.47      (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('simpl_trail', [status(thm)], ['28', '75'])).
% 1.28/1.47  thf(t47_xboole_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.28/1.47  thf('77', plain,
% 1.28/1.47      (![X26 : $i, X27 : $i]:
% 1.28/1.47         ((k4_xboole_0 @ X26 @ (k3_xboole_0 @ X26 @ X27))
% 1.28/1.47           = (k4_xboole_0 @ X26 @ X27))),
% 1.28/1.47      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.28/1.47  thf('78', plain,
% 1.28/1.47      (![X21 : $i, X22 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 1.28/1.47           = (k2_xboole_0 @ X21 @ X22))),
% 1.28/1.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.28/1.47  thf('79', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.28/1.47           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.28/1.47      inference('sup+', [status(thm)], ['77', '78'])).
% 1.28/1.47  thf('80', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.28/1.47  thf('81', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.28/1.47           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.28/1.47      inference('demod', [status(thm)], ['79', '80'])).
% 1.28/1.47  thf('82', plain,
% 1.28/1.47      (![X28 : $i, X29 : $i]:
% 1.28/1.47         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 1.28/1.47           = (k3_xboole_0 @ X28 @ X29))),
% 1.28/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.28/1.47  thf('83', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.28/1.47      inference('demod', [status(thm)], ['58', '59'])).
% 1.28/1.47  thf('84', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 1.28/1.47      inference('sup+', [status(thm)], ['82', '83'])).
% 1.28/1.47  thf('85', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.28/1.47           = (X1))),
% 1.28/1.47      inference('demod', [status(thm)], ['81', '84'])).
% 1.28/1.47  thf('86', plain,
% 1.28/1.47      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.28/1.47         (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['76', '85'])).
% 1.28/1.47  thf('87', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(t74_tops_1, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( l1_pre_topc @ A ) =>
% 1.28/1.47       ( ![B:$i]:
% 1.28/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.28/1.47           ( ( k1_tops_1 @ A @ B ) =
% 1.28/1.47             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.28/1.47  thf('88', plain,
% 1.28/1.47      (![X63 : $i, X64 : $i]:
% 1.28/1.47         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 1.28/1.47          | ((k1_tops_1 @ X64 @ X63)
% 1.28/1.47              = (k7_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 1.28/1.47                 (k2_tops_1 @ X64 @ X63)))
% 1.28/1.47          | ~ (l1_pre_topc @ X64))),
% 1.28/1.47      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.28/1.47  thf('89', plain,
% 1.28/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.28/1.47        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.28/1.47            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['87', '88'])).
% 1.28/1.47  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('91', plain,
% 1.28/1.47      (((k1_tops_1 @ sk_A @ sk_B)
% 1.28/1.47         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('demod', [status(thm)], ['89', '90'])).
% 1.28/1.47  thf('92', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.28/1.47           = (k4_xboole_0 @ sk_B @ X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['36', '37'])).
% 1.28/1.47  thf('93', plain,
% 1.28/1.47      (((k1_tops_1 @ sk_A @ sk_B)
% 1.28/1.47         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('demod', [status(thm)], ['91', '92'])).
% 1.28/1.47  thf('94', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.28/1.47  thf('95', plain,
% 1.28/1.47      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.28/1.47         = (sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['86', '93', '94'])).
% 1.28/1.47  thf('96', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.28/1.47  thf('97', plain,
% 1.28/1.47      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 1.28/1.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.28/1.47  thf('98', plain,
% 1.28/1.47      (![X47 : $i, X49 : $i]:
% 1.28/1.47         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 1.28/1.47      inference('cnf', [status(esa)], [t3_subset])).
% 1.28/1.47  thf('99', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['97', '98'])).
% 1.28/1.47  thf('100', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.28/1.47      inference('sup+', [status(thm)], ['96', '99'])).
% 1.28/1.47  thf(involutiveness_k3_subset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.28/1.47       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.28/1.47  thf('101', plain,
% 1.28/1.47      (![X36 : $i, X37 : $i]:
% 1.28/1.47         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 1.28/1.47          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 1.28/1.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.28/1.47  thf('102', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.28/1.47           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['100', '101'])).
% 1.28/1.47  thf('103', plain,
% 1.28/1.47      (((k3_subset_1 @ 
% 1.28/1.47         (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.28/1.47         (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.28/1.47         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['95', '102'])).
% 1.28/1.47  thf('104', plain,
% 1.28/1.47      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.28/1.47         = (sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['86', '93', '94'])).
% 1.28/1.47  thf('105', plain,
% 1.28/1.47      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['2', '7'])).
% 1.28/1.47  thf('106', plain,
% 1.28/1.47      (![X12 : $i, X13 : $i]:
% 1.28/1.47         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.28/1.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.28/1.47  thf('107', plain,
% 1.28/1.47      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['105', '106'])).
% 1.28/1.47  thf('108', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.28/1.47  thf('109', plain,
% 1.28/1.47      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.28/1.47         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.28/1.47      inference('demod', [status(thm)], ['107', '108'])).
% 1.28/1.47  thf('110', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.28/1.47      inference('sat_resolution*', [status(thm)], ['30', '73', '74'])).
% 1.28/1.47  thf('111', plain,
% 1.28/1.47      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.28/1.47      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 1.28/1.47  thf('112', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.28/1.47      inference('sup+', [status(thm)], ['96', '99'])).
% 1.28/1.47  thf(d5_subset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.28/1.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.28/1.47  thf('113', plain,
% 1.28/1.47      (![X32 : $i, X33 : $i]:
% 1.28/1.47         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 1.28/1.47          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 1.28/1.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.28/1.47  thf('114', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.28/1.47           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['112', '113'])).
% 1.28/1.47  thf('115', plain,
% 1.28/1.47      (((k3_subset_1 @ (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.28/1.47         (k2_tops_1 @ sk_A @ sk_B))
% 1.28/1.47         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('sup+', [status(thm)], ['111', '114'])).
% 1.28/1.47  thf('116', plain,
% 1.28/1.47      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.28/1.47      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 1.28/1.47  thf('117', plain,
% 1.28/1.47      (((k1_tops_1 @ sk_A @ sk_B)
% 1.28/1.47         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('demod', [status(thm)], ['91', '92'])).
% 1.28/1.47  thf('118', plain,
% 1.28/1.47      (((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.28/1.47         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['115', '116', '117'])).
% 1.28/1.47  thf('119', plain,
% 1.28/1.47      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.28/1.47         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['103', '104', '118'])).
% 1.28/1.47  thf('120', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47              (k1_tops_1 @ sk_A @ sk_B))))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('split', [status(esa)], ['29'])).
% 1.28/1.47  thf('121', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.28/1.47           = (k4_xboole_0 @ sk_B @ X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['36', '37'])).
% 1.28/1.47  thf('122', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(t44_tops_1, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( l1_pre_topc @ A ) =>
% 1.28/1.47       ( ![B:$i]:
% 1.28/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.28/1.47           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.28/1.47  thf('123', plain,
% 1.28/1.47      (![X55 : $i, X56 : $i]:
% 1.28/1.47         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.28/1.47          | (r1_tarski @ (k1_tops_1 @ X56 @ X55) @ X55)
% 1.28/1.47          | ~ (l1_pre_topc @ X56))),
% 1.28/1.47      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.28/1.47  thf('124', plain,
% 1.28/1.47      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.28/1.47      inference('sup-', [status(thm)], ['122', '123'])).
% 1.28/1.47  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('126', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.28/1.47      inference('demod', [status(thm)], ['124', '125'])).
% 1.28/1.47  thf('127', plain,
% 1.28/1.47      (![X47 : $i, X49 : $i]:
% 1.28/1.47         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 1.28/1.47      inference('cnf', [status(esa)], [t3_subset])).
% 1.28/1.47  thf('128', plain,
% 1.28/1.47      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.28/1.47      inference('sup-', [status(thm)], ['126', '127'])).
% 1.28/1.47  thf('129', plain,
% 1.28/1.47      (![X32 : $i, X33 : $i]:
% 1.28/1.47         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 1.28/1.47          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 1.28/1.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.28/1.47  thf('130', plain,
% 1.28/1.47      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.28/1.47         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['128', '129'])).
% 1.28/1.47  thf('131', plain,
% 1.28/1.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.28/1.47      inference('demod', [status(thm)], ['120', '121', '130'])).
% 1.28/1.47  thf('132', plain,
% 1.28/1.47      (~
% 1.28/1.47       (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.28/1.47             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.28/1.47      inference('sat_resolution*', [status(thm)], ['30', '73'])).
% 1.28/1.47  thf('133', plain,
% 1.28/1.47      (((k2_tops_1 @ sk_A @ sk_B)
% 1.28/1.47         != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.28/1.47      inference('simpl_trail', [status(thm)], ['131', '132'])).
% 1.28/1.47  thf('134', plain, ($false),
% 1.28/1.47      inference('simplify_reflect-', [status(thm)], ['119', '133'])).
% 1.28/1.47  
% 1.28/1.47  % SZS output end Refutation
% 1.28/1.47  
% 1.28/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
