%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fp3Qk3PV4g

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:28 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 477 expanded)
%              Number of leaves         :   40 ( 162 expanded)
%              Depth                    :   16
%              Number of atoms          : 1524 (4893 expanded)
%              Number of equality atoms :  101 ( 302 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('6',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ~ ( v3_pre_topc @ X61 @ X62 )
      | ~ ( r1_tarski @ X61 @ X63 )
      | ( r1_tarski @ X61 @ ( k1_tops_1 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( ( k1_tops_1 @ X67 @ X66 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X67 ) @ X66 @ ( k2_tops_1 @ X67 @ X66 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( k2_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( k2_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['19','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_tops_1 @ X60 @ X59 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X60 ) @ ( k2_pre_topc @ X60 @ X59 ) @ ( k1_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( l1_pre_topc @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X53 @ X54 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['44','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('73',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('80',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X43 @ X41 )
        = ( k9_subset_1 @ X42 @ X43 @ ( k3_subset_1 @ X42 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('83',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('86',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('93',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('97',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('103',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 )
      = ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('106',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('108',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k9_subset_1 @ X34 @ X33 @ X33 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','104','109'])).

thf('111',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','110'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('113',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('115',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X57 @ X58 ) @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('116',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','63','64','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fp3Qk3PV4g
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:42:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.14/2.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.14/2.37  % Solved by: fo/fo7.sh
% 2.14/2.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.14/2.37  % done 6312 iterations in 1.909s
% 2.14/2.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.14/2.37  % SZS output start Refutation
% 2.14/2.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.14/2.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.14/2.37  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.14/2.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.14/2.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.14/2.37  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.14/2.37  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.14/2.37  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.14/2.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.14/2.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.14/2.37  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.14/2.37  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.14/2.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.14/2.37  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.14/2.37  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.14/2.37  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.14/2.37  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.14/2.37  thf(sk_B_type, type, sk_B: $i).
% 2.14/2.37  thf(sk_A_type, type, sk_A: $i).
% 2.14/2.37  thf(t76_tops_1, conjecture,
% 2.14/2.37    (![A:$i]:
% 2.14/2.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.14/2.37       ( ![B:$i]:
% 2.14/2.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.14/2.37           ( ( v3_pre_topc @ B @ A ) <=>
% 2.14/2.37             ( ( k2_tops_1 @ A @ B ) =
% 2.14/2.37               ( k7_subset_1 @
% 2.14/2.37                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 2.14/2.37  thf(zf_stmt_0, negated_conjecture,
% 2.14/2.37    (~( ![A:$i]:
% 2.14/2.37        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.14/2.37          ( ![B:$i]:
% 2.14/2.37            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.14/2.37              ( ( v3_pre_topc @ B @ A ) <=>
% 2.14/2.37                ( ( k2_tops_1 @ A @ B ) =
% 2.14/2.37                  ( k7_subset_1 @
% 2.14/2.37                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 2.14/2.37    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 2.14/2.37  thf('0', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 2.14/2.37        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('1', plain,
% 2.14/2.37      (~
% 2.14/2.37       (((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.14/2.37       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('split', [status(esa)], ['0'])).
% 2.14/2.37  thf('2', plain,
% 2.14/2.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('3', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 2.14/2.37        | (v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('4', plain,
% 2.14/2.37      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('split', [status(esa)], ['3'])).
% 2.14/2.37  thf('5', plain,
% 2.14/2.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf(t56_tops_1, axiom,
% 2.14/2.37    (![A:$i]:
% 2.14/2.37     ( ( l1_pre_topc @ A ) =>
% 2.14/2.37       ( ![B:$i]:
% 2.14/2.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.14/2.37           ( ![C:$i]:
% 2.14/2.37             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.14/2.37               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.14/2.37                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.14/2.37  thf('6', plain,
% 2.14/2.37      (![X61 : $i, X62 : $i, X63 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 2.14/2.37          | ~ (v3_pre_topc @ X61 @ X62)
% 2.14/2.37          | ~ (r1_tarski @ X61 @ X63)
% 2.14/2.37          | (r1_tarski @ X61 @ (k1_tops_1 @ X62 @ X63))
% 2.14/2.37          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 2.14/2.37          | ~ (l1_pre_topc @ X62))),
% 2.14/2.37      inference('cnf', [status(esa)], [t56_tops_1])).
% 2.14/2.37  thf('7', plain,
% 2.14/2.37      (![X0 : $i]:
% 2.14/2.37         (~ (l1_pre_topc @ sk_A)
% 2.14/2.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.14/2.37          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.14/2.37          | ~ (r1_tarski @ sk_B @ X0)
% 2.14/2.37          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('sup-', [status(thm)], ['5', '6'])).
% 2.14/2.37  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('9', plain,
% 2.14/2.37      (![X0 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.14/2.37          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.14/2.37          | ~ (r1_tarski @ sk_B @ X0)
% 2.14/2.37          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('demod', [status(thm)], ['7', '8'])).
% 2.14/2.37  thf('10', plain,
% 2.14/2.37      ((![X0 : $i]:
% 2.14/2.37          (~ (r1_tarski @ sk_B @ X0)
% 2.14/2.37           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.14/2.37           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.14/2.37         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('sup-', [status(thm)], ['4', '9'])).
% 2.14/2.37  thf('11', plain,
% 2.14/2.37      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.14/2.37         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('sup-', [status(thm)], ['2', '10'])).
% 2.14/2.37  thf(d10_xboole_0, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.14/2.37  thf('12', plain,
% 2.14/2.37      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.14/2.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.14/2.37  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.14/2.37      inference('simplify', [status(thm)], ['12'])).
% 2.14/2.37  thf('14', plain,
% 2.14/2.37      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.14/2.37         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('demod', [status(thm)], ['11', '13'])).
% 2.14/2.37  thf('15', plain,
% 2.14/2.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf(t3_subset, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.14/2.37  thf('16', plain,
% 2.14/2.37      (![X47 : $i, X48 : $i]:
% 2.14/2.37         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 2.14/2.37      inference('cnf', [status(esa)], [t3_subset])).
% 2.14/2.37  thf('17', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.14/2.37      inference('sup-', [status(thm)], ['15', '16'])).
% 2.14/2.37  thf(t28_xboole_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.14/2.37  thf('18', plain,
% 2.14/2.37      (![X15 : $i, X16 : $i]:
% 2.14/2.37         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 2.14/2.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.14/2.37  thf('19', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 2.14/2.37      inference('sup-', [status(thm)], ['17', '18'])).
% 2.14/2.37  thf(commutativity_k3_xboole_0, axiom,
% 2.14/2.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.14/2.37  thf('20', plain,
% 2.14/2.37      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.14/2.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.14/2.37  thf(t48_xboole_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.14/2.37  thf('21', plain,
% 2.14/2.37      (![X27 : $i, X28 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 2.14/2.37           = (k3_xboole_0 @ X27 @ X28))),
% 2.14/2.37      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.14/2.37  thf(t36_xboole_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.14/2.37  thf('22', plain,
% 2.14/2.37      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 2.14/2.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.14/2.37  thf('23', plain,
% 2.14/2.37      (![X47 : $i, X49 : $i]:
% 2.14/2.37         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 2.14/2.37      inference('cnf', [status(esa)], [t3_subset])).
% 2.14/2.37  thf('24', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['22', '23'])).
% 2.14/2.37  thf('25', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 2.14/2.37      inference('sup+', [status(thm)], ['21', '24'])).
% 2.14/2.37  thf('26', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 2.14/2.37      inference('sup+', [status(thm)], ['20', '25'])).
% 2.14/2.37  thf(t74_tops_1, axiom,
% 2.14/2.37    (![A:$i]:
% 2.14/2.37     ( ( l1_pre_topc @ A ) =>
% 2.14/2.37       ( ![B:$i]:
% 2.14/2.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.14/2.37           ( ( k1_tops_1 @ A @ B ) =
% 2.14/2.37             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.14/2.37  thf('27', plain,
% 2.14/2.37      (![X66 : $i, X67 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 2.14/2.37          | ((k1_tops_1 @ X67 @ X66)
% 2.14/2.37              = (k7_subset_1 @ (u1_struct_0 @ X67) @ X66 @ 
% 2.14/2.37                 (k2_tops_1 @ X67 @ X66)))
% 2.14/2.37          | ~ (l1_pre_topc @ X67))),
% 2.14/2.37      inference('cnf', [status(esa)], [t74_tops_1])).
% 2.14/2.37  thf('28', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (~ (l1_pre_topc @ X0)
% 2.14/2.37          | ((k1_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 2.14/2.37              = (k7_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.14/2.37                 (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ 
% 2.14/2.37                 (k2_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))),
% 2.14/2.37      inference('sup-', [status(thm)], ['26', '27'])).
% 2.14/2.37  thf('29', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 2.14/2.37      inference('sup+', [status(thm)], ['20', '25'])).
% 2.14/2.37  thf(redefinition_k7_subset_1, axiom,
% 2.14/2.37    (![A:$i,B:$i,C:$i]:
% 2.14/2.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.14/2.37       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.14/2.37  thf('30', plain,
% 2.14/2.37      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 2.14/2.37          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 2.14/2.37      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.14/2.37  thf('31', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.37         ((k7_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.14/2.37           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.14/2.37      inference('sup-', [status(thm)], ['29', '30'])).
% 2.14/2.37  thf('32', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (~ (l1_pre_topc @ X0)
% 2.14/2.37          | ((k1_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 2.14/2.37              = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ 
% 2.14/2.37                 (k2_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))),
% 2.14/2.37      inference('demod', [status(thm)], ['28', '31'])).
% 2.14/2.37  thf('33', plain,
% 2.14/2.37      ((((k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 2.14/2.37          = (k4_xboole_0 @ sk_B @ 
% 2.14/2.37             (k2_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))))
% 2.14/2.37        | ~ (l1_pre_topc @ sk_A))),
% 2.14/2.37      inference('sup+', [status(thm)], ['19', '32'])).
% 2.14/2.37  thf('34', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 2.14/2.37      inference('sup-', [status(thm)], ['17', '18'])).
% 2.14/2.37  thf('35', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 2.14/2.37      inference('sup-', [status(thm)], ['17', '18'])).
% 2.14/2.37  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('37', plain,
% 2.14/2.37      (((k1_tops_1 @ sk_A @ sk_B)
% 2.14/2.37         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.14/2.37      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 2.14/2.37  thf('38', plain,
% 2.14/2.37      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 2.14/2.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.14/2.37  thf('39', plain,
% 2.14/2.37      (![X4 : $i, X6 : $i]:
% 2.14/2.37         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.14/2.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.14/2.37  thf('40', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.14/2.37          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.14/2.37      inference('sup-', [status(thm)], ['38', '39'])).
% 2.14/2.37  thf('41', plain,
% 2.14/2.37      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.14/2.37        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.14/2.37      inference('sup-', [status(thm)], ['37', '40'])).
% 2.14/2.37  thf('42', plain,
% 2.14/2.37      (((k1_tops_1 @ sk_A @ sk_B)
% 2.14/2.37         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.14/2.37      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 2.14/2.37  thf('43', plain,
% 2.14/2.37      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.14/2.37        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 2.14/2.37      inference('demod', [status(thm)], ['41', '42'])).
% 2.14/2.37  thf('44', plain,
% 2.14/2.37      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 2.14/2.37         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('sup-', [status(thm)], ['14', '43'])).
% 2.14/2.37  thf('45', plain,
% 2.14/2.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf(l78_tops_1, axiom,
% 2.14/2.37    (![A:$i]:
% 2.14/2.37     ( ( l1_pre_topc @ A ) =>
% 2.14/2.37       ( ![B:$i]:
% 2.14/2.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.14/2.37           ( ( k2_tops_1 @ A @ B ) =
% 2.14/2.37             ( k7_subset_1 @
% 2.14/2.37               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.14/2.37               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.14/2.37  thf('46', plain,
% 2.14/2.37      (![X59 : $i, X60 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 2.14/2.37          | ((k2_tops_1 @ X60 @ X59)
% 2.14/2.37              = (k7_subset_1 @ (u1_struct_0 @ X60) @ 
% 2.14/2.37                 (k2_pre_topc @ X60 @ X59) @ (k1_tops_1 @ X60 @ X59)))
% 2.14/2.37          | ~ (l1_pre_topc @ X60))),
% 2.14/2.37      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.14/2.37  thf('47', plain,
% 2.14/2.37      ((~ (l1_pre_topc @ sk_A)
% 2.14/2.37        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.14/2.37      inference('sup-', [status(thm)], ['45', '46'])).
% 2.14/2.37  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('49', plain,
% 2.14/2.37      (((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.14/2.37            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.14/2.37      inference('demod', [status(thm)], ['47', '48'])).
% 2.14/2.37  thf('50', plain,
% 2.14/2.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf(dt_k2_pre_topc, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( ( l1_pre_topc @ A ) & 
% 2.14/2.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.14/2.37       ( m1_subset_1 @
% 2.14/2.37         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.14/2.37  thf('51', plain,
% 2.14/2.37      (![X53 : $i, X54 : $i]:
% 2.14/2.37         (~ (l1_pre_topc @ X53)
% 2.14/2.37          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 2.14/2.37          | (m1_subset_1 @ (k2_pre_topc @ X53 @ X54) @ 
% 2.14/2.37             (k1_zfmisc_1 @ (u1_struct_0 @ X53))))),
% 2.14/2.37      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.14/2.37  thf('52', plain,
% 2.14/2.37      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.14/2.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.14/2.37        | ~ (l1_pre_topc @ sk_A))),
% 2.14/2.37      inference('sup-', [status(thm)], ['50', '51'])).
% 2.14/2.37  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('54', plain,
% 2.14/2.37      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.14/2.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.14/2.37      inference('demod', [status(thm)], ['52', '53'])).
% 2.14/2.37  thf('55', plain,
% 2.14/2.37      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 2.14/2.37          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 2.14/2.37      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.14/2.37  thf('56', plain,
% 2.14/2.37      (![X0 : $i]:
% 2.14/2.37         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.14/2.37           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['54', '55'])).
% 2.14/2.37  thf('57', plain,
% 2.14/2.37      (((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.14/2.37            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.14/2.37      inference('demod', [status(thm)], ['49', '56'])).
% 2.14/2.37  thf('58', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.14/2.37         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('sup+', [status(thm)], ['44', '57'])).
% 2.14/2.37  thf('59', plain,
% 2.14/2.37      (![X0 : $i]:
% 2.14/2.37         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.14/2.37           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['54', '55'])).
% 2.14/2.37  thf('60', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.14/2.37         <= (~
% 2.14/2.37             (((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.14/2.37      inference('split', [status(esa)], ['0'])).
% 2.14/2.37  thf('61', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.14/2.37         <= (~
% 2.14/2.37             (((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.14/2.37      inference('sup-', [status(thm)], ['59', '60'])).
% 2.14/2.37  thf('62', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 2.14/2.37         <= (~
% 2.14/2.37             (((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 2.14/2.37             ((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('sup-', [status(thm)], ['58', '61'])).
% 2.14/2.37  thf('63', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.14/2.37       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('simplify', [status(thm)], ['62'])).
% 2.14/2.37  thf('64', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.14/2.37       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('split', [status(esa)], ['3'])).
% 2.14/2.37  thf('65', plain,
% 2.14/2.37      (![X0 : $i]:
% 2.14/2.37         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.14/2.37           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['54', '55'])).
% 2.14/2.37  thf('66', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.14/2.37         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.14/2.37      inference('split', [status(esa)], ['3'])).
% 2.14/2.37  thf('67', plain,
% 2.14/2.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.14/2.37         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.14/2.37      inference('sup+', [status(thm)], ['65', '66'])).
% 2.14/2.37  thf(commutativity_k2_xboole_0, axiom,
% 2.14/2.37    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.14/2.37  thf('68', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.14/2.37      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.14/2.37  thf(t46_xboole_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 2.14/2.37  thf('69', plain,
% 2.14/2.37      (![X25 : $i, X26 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 2.14/2.37      inference('cnf', [status(esa)], [t46_xboole_1])).
% 2.14/2.37  thf('70', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.14/2.37      inference('sup+', [status(thm)], ['68', '69'])).
% 2.14/2.37  thf('71', plain,
% 2.14/2.37      (![X27 : $i, X28 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 2.14/2.37           = (k3_xboole_0 @ X27 @ X28))),
% 2.14/2.37      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.14/2.37  thf('72', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.14/2.37           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('sup+', [status(thm)], ['70', '71'])).
% 2.14/2.37  thf(t3_boole, axiom,
% 2.14/2.37    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.14/2.37  thf('73', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 2.14/2.37      inference('cnf', [status(esa)], [t3_boole])).
% 2.14/2.37  thf('74', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('demod', [status(thm)], ['72', '73'])).
% 2.14/2.37  thf('75', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 2.14/2.37      inference('sup+', [status(thm)], ['20', '25'])).
% 2.14/2.37  thf('76', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('sup+', [status(thm)], ['74', '75'])).
% 2.14/2.37  thf(t40_xboole_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.14/2.37  thf('77', plain,
% 2.14/2.37      (![X20 : $i, X21 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 2.14/2.37           = (k4_xboole_0 @ X20 @ X21))),
% 2.14/2.37      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.14/2.37  thf('78', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['22', '23'])).
% 2.14/2.37  thf('79', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.14/2.37          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('sup+', [status(thm)], ['77', '78'])).
% 2.14/2.37  thf(t32_subset_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.14/2.37       ( ![C:$i]:
% 2.14/2.37         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.14/2.37           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.14/2.37             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.14/2.37  thf('80', plain,
% 2.14/2.37      (![X41 : $i, X42 : $i, X43 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 2.14/2.37          | ((k7_subset_1 @ X42 @ X43 @ X41)
% 2.14/2.37              = (k9_subset_1 @ X42 @ X43 @ (k3_subset_1 @ X42 @ X41)))
% 2.14/2.37          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 2.14/2.37      inference('cnf', [status(esa)], [t32_subset_1])).
% 2.14/2.37  thf('81', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.14/2.37          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 2.14/2.37              (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 2.14/2.37                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 2.14/2.37                  (k4_xboole_0 @ X1 @ X0)))))),
% 2.14/2.37      inference('sup-', [status(thm)], ['79', '80'])).
% 2.14/2.37  thf('82', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('sup+', [status(thm)], ['74', '75'])).
% 2.14/2.37  thf(involutiveness_k3_subset_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.14/2.37       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.14/2.37  thf('83', plain,
% 2.14/2.37      (![X36 : $i, X37 : $i]:
% 2.14/2.37         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 2.14/2.37          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 2.14/2.37      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.14/2.37  thf('84', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 2.14/2.37           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['82', '83'])).
% 2.14/2.37  thf('85', plain,
% 2.14/2.37      (![X20 : $i, X21 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 2.14/2.37           = (k4_xboole_0 @ X20 @ X21))),
% 2.14/2.37      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.14/2.37  thf('86', plain,
% 2.14/2.37      (![X27 : $i, X28 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 2.14/2.37           = (k3_xboole_0 @ X27 @ X28))),
% 2.14/2.37      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.14/2.37  thf('87', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 2.14/2.37      inference('sup+', [status(thm)], ['85', '86'])).
% 2.14/2.37  thf('88', plain,
% 2.14/2.37      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.14/2.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.14/2.37  thf('89', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('demod', [status(thm)], ['87', '88'])).
% 2.14/2.37  thf('90', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('demod', [status(thm)], ['72', '73'])).
% 2.14/2.37  thf('91', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37           = (X0))),
% 2.14/2.37      inference('demod', [status(thm)], ['89', '90'])).
% 2.14/2.37  thf('92', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['22', '23'])).
% 2.14/2.37  thf(d5_subset_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.14/2.37       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.14/2.37  thf('93', plain,
% 2.14/2.37      (![X29 : $i, X30 : $i]:
% 2.14/2.37         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 2.14/2.37          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 2.14/2.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.14/2.37  thf('94', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.14/2.37           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.14/2.37      inference('sup-', [status(thm)], ['92', '93'])).
% 2.14/2.37  thf('95', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 2.14/2.37           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))
% 2.14/2.37           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 2.14/2.37      inference('sup+', [status(thm)], ['91', '94'])).
% 2.14/2.37  thf('96', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37           = (X0))),
% 2.14/2.37      inference('demod', [status(thm)], ['89', '90'])).
% 2.14/2.37  thf('97', plain,
% 2.14/2.37      (![X20 : $i, X21 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 2.14/2.37           = (k4_xboole_0 @ X20 @ X21))),
% 2.14/2.37      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.14/2.37  thf('98', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 2.14/2.37           = (k4_xboole_0 @ X1 @ X0))),
% 2.14/2.37      inference('demod', [status(thm)], ['95', '96', '97'])).
% 2.14/2.37  thf('99', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37           = (X0))),
% 2.14/2.37      inference('demod', [status(thm)], ['84', '98'])).
% 2.14/2.37  thf('100', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.14/2.37          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 2.14/2.37              (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X0)))),
% 2.14/2.37      inference('demod', [status(thm)], ['81', '99'])).
% 2.14/2.37  thf('101', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 2.14/2.37           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['76', '100'])).
% 2.14/2.37  thf('102', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.14/2.37      inference('sup+', [status(thm)], ['74', '75'])).
% 2.14/2.37  thf('103', plain,
% 2.14/2.37      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.14/2.37         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 2.14/2.37          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 2.14/2.37      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.14/2.37  thf('104', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.37         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2)
% 2.14/2.37           = (k4_xboole_0 @ X0 @ X2))),
% 2.14/2.37      inference('sup-', [status(thm)], ['102', '103'])).
% 2.14/2.37  thf('105', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.14/2.37      inference('simplify', [status(thm)], ['12'])).
% 2.14/2.37  thf('106', plain,
% 2.14/2.37      (![X47 : $i, X49 : $i]:
% 2.14/2.37         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 2.14/2.37      inference('cnf', [status(esa)], [t3_subset])).
% 2.14/2.37  thf('107', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.14/2.37      inference('sup-', [status(thm)], ['105', '106'])).
% 2.14/2.37  thf(idempotence_k9_subset_1, axiom,
% 2.14/2.37    (![A:$i,B:$i,C:$i]:
% 2.14/2.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.14/2.37       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 2.14/2.37  thf('108', plain,
% 2.14/2.37      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.14/2.37         (((k9_subset_1 @ X34 @ X33 @ X33) = (X33))
% 2.14/2.37          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 2.14/2.37      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 2.14/2.37  thf('109', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 2.14/2.37      inference('sup-', [status(thm)], ['107', '108'])).
% 2.14/2.37  thf('110', plain,
% 2.14/2.37      (![X0 : $i, X1 : $i]:
% 2.14/2.37         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.14/2.37      inference('demod', [status(thm)], ['101', '104', '109'])).
% 2.14/2.37  thf('111', plain,
% 2.14/2.37      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 2.14/2.37         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.14/2.37      inference('sup+', [status(thm)], ['67', '110'])).
% 2.14/2.37  thf('112', plain,
% 2.14/2.37      (((k1_tops_1 @ sk_A @ sk_B)
% 2.14/2.37         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.14/2.37      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 2.14/2.37  thf('113', plain,
% 2.14/2.37      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 2.14/2.37         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.14/2.37      inference('sup+', [status(thm)], ['111', '112'])).
% 2.14/2.37  thf('114', plain,
% 2.14/2.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf(fc9_tops_1, axiom,
% 2.14/2.37    (![A:$i,B:$i]:
% 2.14/2.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.14/2.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.14/2.37       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 2.14/2.37  thf('115', plain,
% 2.14/2.37      (![X57 : $i, X58 : $i]:
% 2.14/2.37         (~ (l1_pre_topc @ X57)
% 2.14/2.37          | ~ (v2_pre_topc @ X57)
% 2.14/2.37          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 2.14/2.37          | (v3_pre_topc @ (k1_tops_1 @ X57 @ X58) @ X57))),
% 2.14/2.37      inference('cnf', [status(esa)], [fc9_tops_1])).
% 2.14/2.37  thf('116', plain,
% 2.14/2.37      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 2.14/2.37        | ~ (v2_pre_topc @ sk_A)
% 2.14/2.37        | ~ (l1_pre_topc @ sk_A))),
% 2.14/2.37      inference('sup-', [status(thm)], ['114', '115'])).
% 2.14/2.37  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 2.14/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.37  thf('119', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 2.14/2.37      inference('demod', [status(thm)], ['116', '117', '118'])).
% 2.14/2.37  thf('120', plain,
% 2.14/2.37      (((v3_pre_topc @ sk_B @ sk_A))
% 2.14/2.37         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.14/2.37      inference('sup+', [status(thm)], ['113', '119'])).
% 2.14/2.37  thf('121', plain,
% 2.14/2.37      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 2.14/2.37      inference('split', [status(esa)], ['0'])).
% 2.14/2.37  thf('122', plain,
% 2.14/2.37      (~
% 2.14/2.37       (((k2_tops_1 @ sk_A @ sk_B)
% 2.14/2.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.14/2.37             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.14/2.37       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.14/2.37      inference('sup-', [status(thm)], ['120', '121'])).
% 2.14/2.37  thf('123', plain, ($false),
% 2.14/2.37      inference('sat_resolution*', [status(thm)], ['1', '63', '64', '122'])).
% 2.14/2.37  
% 2.14/2.37  % SZS output end Refutation
% 2.14/2.37  
% 2.14/2.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
