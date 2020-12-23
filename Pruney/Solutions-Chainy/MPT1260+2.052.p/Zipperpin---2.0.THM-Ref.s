%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hXPNMkGhzV

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:30 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  186 (1613 expanded)
%              Number of leaves         :   31 ( 476 expanded)
%              Depth                    :   26
%              Number of atoms          : 1799 (20834 expanded)
%              Number of equality atoms :  125 (1314 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

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

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v3_pre_topc @ X45 @ X44 )
      | ( ( k1_tops_1 @ X44 @ X45 )
        = X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
        | ~ ( v3_pre_topc @ X45 @ X44 )
        | ( ( k1_tops_1 @ X44 @ X45 )
          = X45 ) )
   <= ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
        | ~ ( v3_pre_topc @ X45 @ X44 )
        | ( ( k1_tops_1 @ X44 @ X45 )
          = X45 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 ) )
   <= ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
        | ~ ( v3_pre_topc @ X45 @ X44 )
        | ( ( k1_tops_1 @ X44 @ X45 )
          = X45 ) )
    | ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v3_pre_topc @ X45 @ X44 )
      | ( ( k1_tops_1 @ X44 @ X45 )
        = X45 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v3_pre_topc @ X45 @ X44 )
      | ( ( k1_tops_1 @ X44 @ X45 )
        = X45 ) ) ),
    inference(simpl_trail,[status(thm)],['7','15'])).

thf('17',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k1_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k4_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('66',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ X42 ) @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('72',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('73',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('75',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X36 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('83',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( r1_tarski @ X38 @ ( k2_pre_topc @ X39 @ X38 ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('90',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['81','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('93',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('96',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','98'])).

thf('100',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k1_tops_1 @ X47 @ X46 )
       != X46 )
      | ( v3_pre_topc @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('103',plain,
    ( ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 )
        | ( ( k1_tops_1 @ X47 @ X46 )
         != X46 )
        | ( v3_pre_topc @ X46 @ X47 ) )
   <= ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 )
        | ( ( k1_tops_1 @ X47 @ X46 )
         != X46 )
        | ( v3_pre_topc @ X46 @ X47 ) ) ),
    inference(split,[status(esa)],['102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) )
   <= ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(split,[status(esa)],['102'])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ~ ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ! [X46: $i,X47: $i] :
        ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( l1_pre_topc @ X47 )
        | ~ ( v2_pre_topc @ X47 )
        | ( ( k1_tops_1 @ X47 @ X46 )
         != X46 )
        | ( v3_pre_topc @ X46 @ X47 ) )
    | ! [X44: $i,X45: $i] :
        ( ~ ( l1_pre_topc @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(split,[status(esa)],['102'])).

thf('110',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( ( k1_tops_1 @ X47 @ X46 )
       != X46 )
      | ( v3_pre_topc @ X46 @ X47 ) ) ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( ( k1_tops_1 @ X47 @ X46 )
       != X46 )
      | ( v3_pre_topc @ X46 @ X47 ) ) ),
    inference(simpl_trail,[status(thm)],['103','110'])).

thf('112',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ X42 ) @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('122',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('124',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('126',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('127',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('129',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['86','87'])).

thf('132',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('134',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','98','133'])).

thf('135',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['132','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('137',plain,
    ( sk_B
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','135','136'])).

thf('138',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('139',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('140',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('147',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('148',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,
    ( sk_B
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','135','136'])).

thf('150',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['145','148','149'])).

thf('151',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['115','150'])).

thf('152',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['100','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hXPNMkGhzV
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.73/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.73/1.92  % Solved by: fo/fo7.sh
% 1.73/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.73/1.92  % done 3515 iterations in 1.478s
% 1.73/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.73/1.92  % SZS output start Refutation
% 1.73/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.73/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.73/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.73/1.92  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.73/1.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.73/1.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.73/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.73/1.92  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.73/1.92  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.73/1.92  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.73/1.92  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.73/1.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.73/1.92  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.73/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.73/1.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.73/1.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.73/1.92  thf(t76_tops_1, conjecture,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ( v3_pre_topc @ B @ A ) <=>
% 1.73/1.92             ( ( k2_tops_1 @ A @ B ) =
% 1.73/1.92               ( k7_subset_1 @
% 1.73/1.92                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.73/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.73/1.92    (~( ![A:$i]:
% 1.73/1.92        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.73/1.92          ( ![B:$i]:
% 1.73/1.92            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92              ( ( v3_pre_topc @ B @ A ) <=>
% 1.73/1.92                ( ( k2_tops_1 @ A @ B ) =
% 1.73/1.92                  ( k7_subset_1 @
% 1.73/1.92                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.73/1.92    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.73/1.92  thf('0', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.73/1.92        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('1', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('split', [status(esa)], ['0'])).
% 1.73/1.92  thf('2', plain,
% 1.73/1.92      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 1.73/1.92       ~
% 1.73/1.92       (((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.73/1.92      inference('split', [status(esa)], ['0'])).
% 1.73/1.92  thf('3', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.73/1.92        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('4', plain,
% 1.73/1.92      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('split', [status(esa)], ['3'])).
% 1.73/1.92  thf('5', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(t55_tops_1, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( l1_pre_topc @ B ) =>
% 1.73/1.92           ( ![C:$i]:
% 1.73/1.92             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92               ( ![D:$i]:
% 1.73/1.92                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.73/1.92                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.73/1.92                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.73/1.92                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.73/1.92                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.73/1.92  thf('6', plain,
% 1.73/1.92      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.73/1.92         (~ (l1_pre_topc @ X44)
% 1.73/1.92          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.73/1.92          | ~ (v3_pre_topc @ X45 @ X44)
% 1.73/1.92          | ((k1_tops_1 @ X44 @ X45) = (X45))
% 1.73/1.92          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92          | ~ (l1_pre_topc @ X47)
% 1.73/1.92          | ~ (v2_pre_topc @ X47))),
% 1.73/1.92      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.73/1.92  thf('7', plain,
% 1.73/1.92      ((![X44 : $i, X45 : $i]:
% 1.73/1.92          (~ (l1_pre_topc @ X44)
% 1.73/1.92           | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.73/1.92           | ~ (v3_pre_topc @ X45 @ X44)
% 1.73/1.92           | ((k1_tops_1 @ X44 @ X45) = (X45))))
% 1.73/1.92         <= ((![X44 : $i, X45 : $i]:
% 1.73/1.92                (~ (l1_pre_topc @ X44)
% 1.73/1.92                 | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.73/1.92                 | ~ (v3_pre_topc @ X45 @ X44)
% 1.73/1.92                 | ((k1_tops_1 @ X44 @ X45) = (X45)))))),
% 1.73/1.92      inference('split', [status(esa)], ['6'])).
% 1.73/1.92  thf('8', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('9', plain,
% 1.73/1.92      ((![X46 : $i, X47 : $i]:
% 1.73/1.92          (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92           | ~ (l1_pre_topc @ X47)
% 1.73/1.92           | ~ (v2_pre_topc @ X47)))
% 1.73/1.92         <= ((![X46 : $i, X47 : $i]:
% 1.73/1.92                (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92                 | ~ (l1_pre_topc @ X47)
% 1.73/1.92                 | ~ (v2_pre_topc @ X47))))),
% 1.73/1.92      inference('split', [status(esa)], ['6'])).
% 1.73/1.92  thf('10', plain,
% 1.73/1.92      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 1.73/1.92         <= ((![X46 : $i, X47 : $i]:
% 1.73/1.92                (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92                 | ~ (l1_pre_topc @ X47)
% 1.73/1.92                 | ~ (v2_pre_topc @ X47))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['8', '9'])).
% 1.73/1.92  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('13', plain,
% 1.73/1.92      (~
% 1.73/1.92       (![X46 : $i, X47 : $i]:
% 1.73/1.92          (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92           | ~ (l1_pre_topc @ X47)
% 1.73/1.92           | ~ (v2_pre_topc @ X47)))),
% 1.73/1.92      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.73/1.92  thf('14', plain,
% 1.73/1.92      ((![X44 : $i, X45 : $i]:
% 1.73/1.92          (~ (l1_pre_topc @ X44)
% 1.73/1.92           | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.73/1.92           | ~ (v3_pre_topc @ X45 @ X44)
% 1.73/1.92           | ((k1_tops_1 @ X44 @ X45) = (X45)))) | 
% 1.73/1.92       (![X46 : $i, X47 : $i]:
% 1.73/1.92          (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92           | ~ (l1_pre_topc @ X47)
% 1.73/1.92           | ~ (v2_pre_topc @ X47)))),
% 1.73/1.92      inference('split', [status(esa)], ['6'])).
% 1.73/1.92  thf('15', plain,
% 1.73/1.92      ((![X44 : $i, X45 : $i]:
% 1.73/1.92          (~ (l1_pre_topc @ X44)
% 1.73/1.92           | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.73/1.92           | ~ (v3_pre_topc @ X45 @ X44)
% 1.73/1.92           | ((k1_tops_1 @ X44 @ X45) = (X45))))),
% 1.73/1.92      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 1.73/1.92  thf('16', plain,
% 1.73/1.92      (![X44 : $i, X45 : $i]:
% 1.73/1.92         (~ (l1_pre_topc @ X44)
% 1.73/1.92          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.73/1.92          | ~ (v3_pre_topc @ X45 @ X44)
% 1.73/1.92          | ((k1_tops_1 @ X44 @ X45) = (X45)))),
% 1.73/1.92      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 1.73/1.92  thf('17', plain,
% 1.73/1.92      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 1.73/1.92        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 1.73/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['5', '16'])).
% 1.73/1.92  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('19', plain,
% 1.73/1.92      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('demod', [status(thm)], ['17', '18'])).
% 1.73/1.92  thf('20', plain,
% 1.73/1.92      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['4', '19'])).
% 1.73/1.92  thf('21', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(t74_tops_1, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ( k1_tops_1 @ A @ B ) =
% 1.73/1.92             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.73/1.92  thf('22', plain,
% 1.73/1.92      (![X48 : $i, X49 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.73/1.92          | ((k1_tops_1 @ X49 @ X48)
% 1.73/1.92              = (k7_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 1.73/1.92                 (k2_tops_1 @ X49 @ X48)))
% 1.73/1.92          | ~ (l1_pre_topc @ X49))),
% 1.73/1.92      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.73/1.92  thf('23', plain,
% 1.73/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.73/1.92        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.73/1.92            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.73/1.92               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['21', '22'])).
% 1.73/1.92  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('25', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(redefinition_k7_subset_1, axiom,
% 1.73/1.92    (![A:$i,B:$i,C:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.73/1.92  thf('26', plain,
% 1.73/1.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.73/1.92          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.73/1.92      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.73/1.92  thf('27', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.73/1.92           = (k4_xboole_0 @ sk_B @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['25', '26'])).
% 1.73/1.92  thf('28', plain,
% 1.73/1.92      (((k1_tops_1 @ sk_A @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['23', '24', '27'])).
% 1.73/1.92  thf(t48_xboole_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.73/1.92  thf('29', plain,
% 1.73/1.92      (![X14 : $i, X15 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.73/1.92           = (k3_xboole_0 @ X14 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf('30', plain,
% 1.73/1.92      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.73/1.92         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['28', '29'])).
% 1.73/1.92  thf('31', plain,
% 1.73/1.92      ((((k4_xboole_0 @ sk_B @ sk_B)
% 1.73/1.92          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['20', '30'])).
% 1.73/1.92  thf(d10_xboole_0, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.73/1.92  thf('32', plain,
% 1.73/1.92      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.73/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.92  thf('33', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.73/1.92      inference('simplify', [status(thm)], ['32'])).
% 1.73/1.92  thf(t28_xboole_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.73/1.92  thf('34', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i]:
% 1.73/1.92         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.73/1.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.73/1.92  thf('35', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['33', '34'])).
% 1.73/1.92  thf(commutativity_k3_xboole_0, axiom,
% 1.73/1.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.73/1.92  thf('36', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.73/1.92  thf(t100_xboole_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.73/1.92  thf('37', plain,
% 1.73/1.92      (![X5 : $i, X6 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X5 @ X6)
% 1.73/1.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.73/1.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.92  thf('38', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X0 @ X1)
% 1.73/1.92           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['36', '37'])).
% 1.73/1.92  thf('39', plain,
% 1.73/1.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.73/1.92      inference('sup+', [status(thm)], ['35', '38'])).
% 1.73/1.92  thf('40', plain,
% 1.73/1.92      ((((k5_xboole_0 @ sk_B @ sk_B)
% 1.73/1.92          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['31', '39'])).
% 1.73/1.92  thf('41', plain,
% 1.73/1.92      (![X14 : $i, X15 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.73/1.92           = (k3_xboole_0 @ X14 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf(t36_xboole_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.73/1.92  thf('42', plain,
% 1.73/1.92      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.73/1.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.73/1.92  thf('43', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.73/1.92      inference('sup+', [status(thm)], ['41', '42'])).
% 1.73/1.92  thf('44', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i]:
% 1.73/1.92         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.73/1.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.73/1.92  thf('45', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.73/1.92           = (k3_xboole_0 @ X0 @ X1))),
% 1.73/1.92      inference('sup-', [status(thm)], ['43', '44'])).
% 1.73/1.92  thf('46', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.73/1.92  thf('47', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.73/1.92           = (k3_xboole_0 @ X0 @ X1))),
% 1.73/1.92      inference('demod', [status(thm)], ['45', '46'])).
% 1.73/1.92  thf('48', plain,
% 1.73/1.92      (![X5 : $i, X6 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X5 @ X6)
% 1.73/1.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.73/1.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.92  thf('49', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.92           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['47', '48'])).
% 1.73/1.92  thf('50', plain,
% 1.73/1.92      (![X5 : $i, X6 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X5 @ X6)
% 1.73/1.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.73/1.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.92  thf('51', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.92           = (k4_xboole_0 @ X1 @ X0))),
% 1.73/1.92      inference('demod', [status(thm)], ['49', '50'])).
% 1.73/1.92  thf('52', plain,
% 1.73/1.92      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 1.73/1.92          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['40', '51'])).
% 1.73/1.92  thf('53', plain,
% 1.73/1.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.73/1.92      inference('sup+', [status(thm)], ['35', '38'])).
% 1.73/1.92  thf('54', plain,
% 1.73/1.92      (![X14 : $i, X15 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.73/1.92           = (k3_xboole_0 @ X14 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf('55', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 1.73/1.92           = (k3_xboole_0 @ X0 @ X0))),
% 1.73/1.92      inference('sup+', [status(thm)], ['53', '54'])).
% 1.73/1.92  thf('56', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['33', '34'])).
% 1.73/1.92  thf('57', plain,
% 1.73/1.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 1.73/1.92      inference('demod', [status(thm)], ['55', '56'])).
% 1.73/1.92  thf('58', plain,
% 1.73/1.92      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['52', '57'])).
% 1.73/1.92  thf('59', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(t3_subset, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.73/1.92  thf('60', plain,
% 1.73/1.92      (![X33 : $i, X34 : $i]:
% 1.73/1.92         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.73/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.73/1.92  thf('61', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['59', '60'])).
% 1.73/1.92  thf(t109_xboole_1, axiom,
% 1.73/1.92    (![A:$i,B:$i,C:$i]:
% 1.73/1.92     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.73/1.92  thf('62', plain,
% 1.73/1.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.73/1.92         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ (k4_xboole_0 @ X7 @ X9) @ X8))),
% 1.73/1.92      inference('cnf', [status(esa)], [t109_xboole_1])).
% 1.73/1.92  thf('63', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['61', '62'])).
% 1.73/1.92  thf('64', plain,
% 1.73/1.92      (![X33 : $i, X35 : $i]:
% 1.73/1.92         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 1.73/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.73/1.92  thf('65', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.73/1.92          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['63', '64'])).
% 1.73/1.92  thf(l78_tops_1, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ( k2_tops_1 @ A @ B ) =
% 1.73/1.92             ( k7_subset_1 @
% 1.73/1.92               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.73/1.92               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.73/1.92  thf('66', plain,
% 1.73/1.92      (![X42 : $i, X43 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.73/1.92          | ((k2_tops_1 @ X43 @ X42)
% 1.73/1.92              = (k7_subset_1 @ (u1_struct_0 @ X43) @ 
% 1.73/1.92                 (k2_pre_topc @ X43 @ X42) @ (k1_tops_1 @ X43 @ X42)))
% 1.73/1.92          | ~ (l1_pre_topc @ X43))),
% 1.73/1.92      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.73/1.92  thf('67', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (l1_pre_topc @ sk_A)
% 1.73/1.92          | ((k2_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.73/1.92              = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                 (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.73/1.92                 (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['65', '66'])).
% 1.73/1.92  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('69', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k2_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.73/1.92           = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.73/1.92              (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.73/1.92      inference('demod', [status(thm)], ['67', '68'])).
% 1.73/1.92  thf('70', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92             (k1_tops_1 @ sk_A @ 
% 1.73/1.92              (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['58', '69'])).
% 1.73/1.92  thf('71', plain,
% 1.73/1.92      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['52', '57'])).
% 1.73/1.92  thf('72', plain,
% 1.73/1.92      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['52', '57'])).
% 1.73/1.92  thf('73', plain,
% 1.73/1.92      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['4', '19'])).
% 1.73/1.92  thf('74', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(dt_k2_pre_topc, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( ( l1_pre_topc @ A ) & 
% 1.73/1.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.73/1.92       ( m1_subset_1 @
% 1.73/1.92         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.73/1.92  thf('75', plain,
% 1.73/1.92      (![X36 : $i, X37 : $i]:
% 1.73/1.92         (~ (l1_pre_topc @ X36)
% 1.73/1.92          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.73/1.92          | (m1_subset_1 @ (k2_pre_topc @ X36 @ X37) @ 
% 1.73/1.92             (k1_zfmisc_1 @ (u1_struct_0 @ X36))))),
% 1.73/1.92      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.73/1.92  thf('76', plain,
% 1.73/1.92      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['74', '75'])).
% 1.73/1.92  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('78', plain,
% 1.73/1.92      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['76', '77'])).
% 1.73/1.92  thf('79', plain,
% 1.73/1.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.73/1.92          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.73/1.92      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.73/1.92  thf('80', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['78', '79'])).
% 1.73/1.92  thf('81', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['70', '71', '72', '73', '80'])).
% 1.73/1.92  thf('82', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(t48_pre_topc, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 1.73/1.92  thf('83', plain,
% 1.73/1.92      (![X38 : $i, X39 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.73/1.92          | (r1_tarski @ X38 @ (k2_pre_topc @ X39 @ X38))
% 1.73/1.92          | ~ (l1_pre_topc @ X39))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_pre_topc])).
% 1.73/1.92  thf('84', plain,
% 1.73/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.73/1.92        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['82', '83'])).
% 1.73/1.92  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('86', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['84', '85'])).
% 1.73/1.92  thf('87', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i]:
% 1.73/1.92         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.73/1.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.73/1.92  thf('88', plain,
% 1.73/1.92      (((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['86', '87'])).
% 1.73/1.92  thf('89', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X0 @ X1)
% 1.73/1.92           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['36', '37'])).
% 1.73/1.92  thf('90', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['88', '89'])).
% 1.73/1.92  thf('91', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['81', '90'])).
% 1.73/1.92  thf('92', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['78', '79'])).
% 1.73/1.92  thf('93', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= (~
% 1.73/1.92             (((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.73/1.92      inference('split', [status(esa)], ['0'])).
% 1.73/1.92  thf('94', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= (~
% 1.73/1.92             (((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['92', '93'])).
% 1.73/1.92  thf('95', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['88', '89'])).
% 1.73/1.92  thf('96', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          != (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= (~
% 1.73/1.92             (((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['94', '95'])).
% 1.73/1.92  thf('97', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.73/1.92         <= (~
% 1.73/1.92             (((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.73/1.92             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['91', '96'])).
% 1.73/1.92  thf('98', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.73/1.92       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('simplify', [status(thm)], ['97'])).
% 1.73/1.92  thf('99', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('sat_resolution*', [status(thm)], ['2', '98'])).
% 1.73/1.92  thf('100', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 1.73/1.92      inference('simpl_trail', [status(thm)], ['1', '99'])).
% 1.73/1.92  thf('101', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('102', plain,
% 1.73/1.92      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.73/1.92         (~ (l1_pre_topc @ X44)
% 1.73/1.92          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.73/1.92          | ((k1_tops_1 @ X47 @ X46) != (X46))
% 1.73/1.92          | (v3_pre_topc @ X46 @ X47)
% 1.73/1.92          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92          | ~ (l1_pre_topc @ X47)
% 1.73/1.92          | ~ (v2_pre_topc @ X47))),
% 1.73/1.92      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.73/1.92  thf('103', plain,
% 1.73/1.92      ((![X46 : $i, X47 : $i]:
% 1.73/1.92          (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92           | ~ (l1_pre_topc @ X47)
% 1.73/1.92           | ~ (v2_pre_topc @ X47)
% 1.73/1.92           | ((k1_tops_1 @ X47 @ X46) != (X46))
% 1.73/1.92           | (v3_pre_topc @ X46 @ X47)))
% 1.73/1.92         <= ((![X46 : $i, X47 : $i]:
% 1.73/1.92                (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92                 | ~ (l1_pre_topc @ X47)
% 1.73/1.92                 | ~ (v2_pre_topc @ X47)
% 1.73/1.92                 | ((k1_tops_1 @ X47 @ X46) != (X46))
% 1.73/1.92                 | (v3_pre_topc @ X46 @ X47))))),
% 1.73/1.92      inference('split', [status(esa)], ['102'])).
% 1.73/1.92  thf('104', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('105', plain,
% 1.73/1.92      ((![X44 : $i, X45 : $i]:
% 1.73/1.92          (~ (l1_pre_topc @ X44)
% 1.73/1.92           | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))))
% 1.73/1.92         <= ((![X44 : $i, X45 : $i]:
% 1.73/1.92                (~ (l1_pre_topc @ X44)
% 1.73/1.92                 | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44))))))),
% 1.73/1.92      inference('split', [status(esa)], ['102'])).
% 1.73/1.92  thf('106', plain,
% 1.73/1.92      ((~ (l1_pre_topc @ sk_A))
% 1.73/1.92         <= ((![X44 : $i, X45 : $i]:
% 1.73/1.92                (~ (l1_pre_topc @ X44)
% 1.73/1.92                 | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44))))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['104', '105'])).
% 1.73/1.92  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('108', plain,
% 1.73/1.92      (~
% 1.73/1.92       (![X44 : $i, X45 : $i]:
% 1.73/1.92          (~ (l1_pre_topc @ X44)
% 1.73/1.92           | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))))),
% 1.73/1.92      inference('demod', [status(thm)], ['106', '107'])).
% 1.73/1.92  thf('109', plain,
% 1.73/1.92      ((![X46 : $i, X47 : $i]:
% 1.73/1.92          (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92           | ~ (l1_pre_topc @ X47)
% 1.73/1.92           | ~ (v2_pre_topc @ X47)
% 1.73/1.92           | ((k1_tops_1 @ X47 @ X46) != (X46))
% 1.73/1.92           | (v3_pre_topc @ X46 @ X47))) | 
% 1.73/1.92       (![X44 : $i, X45 : $i]:
% 1.73/1.92          (~ (l1_pre_topc @ X44)
% 1.73/1.92           | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))))),
% 1.73/1.92      inference('split', [status(esa)], ['102'])).
% 1.73/1.92  thf('110', plain,
% 1.73/1.92      ((![X46 : $i, X47 : $i]:
% 1.73/1.92          (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92           | ~ (l1_pre_topc @ X47)
% 1.73/1.92           | ~ (v2_pre_topc @ X47)
% 1.73/1.92           | ((k1_tops_1 @ X47 @ X46) != (X46))
% 1.73/1.92           | (v3_pre_topc @ X46 @ X47)))),
% 1.73/1.92      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 1.73/1.92  thf('111', plain,
% 1.73/1.92      (![X46 : $i, X47 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.73/1.92          | ~ (l1_pre_topc @ X47)
% 1.73/1.92          | ~ (v2_pre_topc @ X47)
% 1.73/1.92          | ((k1_tops_1 @ X47 @ X46) != (X46))
% 1.73/1.92          | (v3_pre_topc @ X46 @ X47))),
% 1.73/1.92      inference('simpl_trail', [status(thm)], ['103', '110'])).
% 1.73/1.92  thf('112', plain,
% 1.73/1.92      (((v3_pre_topc @ sk_B @ sk_A)
% 1.73/1.92        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 1.73/1.92        | ~ (v2_pre_topc @ sk_A)
% 1.73/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['101', '111'])).
% 1.73/1.92  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('115', plain,
% 1.73/1.92      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['112', '113', '114'])).
% 1.73/1.92  thf('116', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('117', plain,
% 1.73/1.92      (![X42 : $i, X43 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.73/1.92          | ((k2_tops_1 @ X43 @ X42)
% 1.73/1.92              = (k7_subset_1 @ (u1_struct_0 @ X43) @ 
% 1.73/1.92                 (k2_pre_topc @ X43 @ X42) @ (k1_tops_1 @ X43 @ X42)))
% 1.73/1.92          | ~ (l1_pre_topc @ X43))),
% 1.73/1.92      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.73/1.92  thf('118', plain,
% 1.73/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.73/1.92        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['116', '117'])).
% 1.73/1.92  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('120', plain,
% 1.73/1.92      (((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['118', '119'])).
% 1.73/1.92  thf('121', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['78', '79'])).
% 1.73/1.92  thf('122', plain,
% 1.73/1.92      (((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['120', '121'])).
% 1.73/1.92  thf('123', plain,
% 1.73/1.92      (![X14 : $i, X15 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.73/1.92           = (k3_xboole_0 @ X14 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf('124', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.73/1.92         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['122', '123'])).
% 1.73/1.92  thf('125', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.73/1.92           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['78', '79'])).
% 1.73/1.92  thf('126', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.73/1.92      inference('split', [status(esa)], ['3'])).
% 1.73/1.92  thf('127', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.73/1.92      inference('sup+', [status(thm)], ['125', '126'])).
% 1.73/1.92  thf('128', plain,
% 1.73/1.92      (![X14 : $i, X15 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.73/1.92           = (k3_xboole_0 @ X14 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf('129', plain,
% 1.73/1.92      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.73/1.92          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.73/1.92         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.73/1.92      inference('sup+', [status(thm)], ['127', '128'])).
% 1.73/1.92  thf('130', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.73/1.92  thf('131', plain,
% 1.73/1.92      (((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['86', '87'])).
% 1.73/1.92  thf('132', plain,
% 1.73/1.92      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.73/1.92          = (sk_B)))
% 1.73/1.92         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.73/1.92  thf('133', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.73/1.92       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('split', [status(esa)], ['3'])).
% 1.73/1.92  thf('134', plain,
% 1.73/1.92      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.73/1.92      inference('sat_resolution*', [status(thm)], ['2', '98', '133'])).
% 1.73/1.92  thf('135', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.73/1.92         = (sk_B))),
% 1.73/1.92      inference('simpl_trail', [status(thm)], ['132', '134'])).
% 1.73/1.92  thf('136', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.73/1.92  thf('137', plain,
% 1.73/1.92      (((sk_B)
% 1.73/1.92         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.73/1.92            (k2_pre_topc @ sk_A @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['124', '135', '136'])).
% 1.73/1.92  thf('138', plain,
% 1.73/1.92      (![X14 : $i, X15 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.73/1.92           = (k3_xboole_0 @ X14 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf('139', plain,
% 1.73/1.92      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.73/1.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.73/1.92  thf('140', plain,
% 1.73/1.92      (![X2 : $i, X4 : $i]:
% 1.73/1.92         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.73/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.92  thf('141', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.73/1.92          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['139', '140'])).
% 1.73/1.92  thf('142', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.92          | ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['138', '141'])).
% 1.73/1.92  thf('143', plain,
% 1.73/1.92      (![X14 : $i, X15 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.73/1.92           = (k3_xboole_0 @ X14 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf('144', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.92          | ((X1) = (k3_xboole_0 @ X1 @ X0)))),
% 1.73/1.92      inference('demod', [status(thm)], ['142', '143'])).
% 1.73/1.92  thf('145', plain,
% 1.73/1.92      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.73/1.92        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.73/1.92            = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.73/1.92               (k2_pre_topc @ sk_A @ sk_B))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['137', '144'])).
% 1.73/1.92  thf('146', plain,
% 1.73/1.92      (((k1_tops_1 @ sk_A @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['23', '24', '27'])).
% 1.73/1.92  thf('147', plain,
% 1.73/1.92      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.73/1.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.73/1.92  thf('148', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.73/1.92      inference('sup+', [status(thm)], ['146', '147'])).
% 1.73/1.92  thf('149', plain,
% 1.73/1.92      (((sk_B)
% 1.73/1.92         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.73/1.92            (k2_pre_topc @ sk_A @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['124', '135', '136'])).
% 1.73/1.92  thf('150', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['145', '148', '149'])).
% 1.73/1.92  thf('151', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['115', '150'])).
% 1.73/1.92  thf('152', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 1.73/1.92      inference('simplify', [status(thm)], ['151'])).
% 1.73/1.92  thf('153', plain, ($false), inference('demod', [status(thm)], ['100', '152'])).
% 1.73/1.92  
% 1.73/1.92  % SZS output end Refutation
% 1.73/1.92  
% 1.73/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
