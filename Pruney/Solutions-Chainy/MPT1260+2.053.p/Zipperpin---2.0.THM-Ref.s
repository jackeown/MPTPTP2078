%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PSOATw9bS4

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:31 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 549 expanded)
%              Number of leaves         :   31 ( 165 expanded)
%              Depth                    :   21
%              Number of atoms          : 1577 (7534 expanded)
%              Number of equality atoms :   97 ( 387 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ X34 @ ( k2_pre_topc @ X35 @ X34 ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v3_pre_topc @ X41 @ X40 )
      | ( ( k1_tops_1 @ X40 @ X41 )
        = X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('51',plain,
    ( ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( v3_pre_topc @ X41 @ X40 )
        | ( ( k1_tops_1 @ X40 @ X41 )
          = X41 ) )
   <= ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( v3_pre_topc @ X41 @ X40 )
        | ( ( k1_tops_1 @ X40 @ X41 )
          = X41 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 ) )
   <= ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('54',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( v3_pre_topc @ X41 @ X40 )
        | ( ( k1_tops_1 @ X40 @ X41 )
          = X41 ) )
    | ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('59',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v3_pre_topc @ X41 @ X40 )
      | ( ( k1_tops_1 @ X40 @ X41 )
        = X41 ) ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v3_pre_topc @ X41 @ X40 )
      | ( ( k1_tops_1 @ X40 @ X41 )
        = X41 ) ) ),
    inference(simpl_trail,[status(thm)],['51','59'])).

thf('61',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('71',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['47','69','70'])).

thf('72',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['45','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('74',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['43','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['34','79'])).

thf('81',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('90',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k1_tops_1 @ X45 @ X44 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 @ ( k2_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','95'])).

thf('97',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('98',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['34','79'])).

thf('100',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['88','98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('102',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('103',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('105',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('108',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('111',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X43 @ X42 )
       != X42 )
      | ( v3_pre_topc @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('112',plain,
    ( ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 )
        | ( ( k1_tops_1 @ X43 @ X42 )
         != X42 )
        | ( v3_pre_topc @ X42 @ X43 ) )
   <= ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 )
        | ( ( k1_tops_1 @ X43 @ X42 )
         != X42 )
        | ( v3_pre_topc @ X42 @ X43 ) ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
   <= ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ~ ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ! [X42: $i,X43: $i] :
        ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
        | ~ ( l1_pre_topc @ X43 )
        | ~ ( v2_pre_topc @ X43 )
        | ( ( k1_tops_1 @ X43 @ X42 )
         != X42 )
        | ( v3_pre_topc @ X42 @ X43 ) )
    | ! [X40: $i,X41: $i] :
        ( ~ ( l1_pre_topc @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('119',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( ( k1_tops_1 @ X43 @ X42 )
       != X42 )
      | ( v3_pre_topc @ X42 @ X43 ) ) ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( ( k1_tops_1 @ X43 @ X42 )
       != X42 )
      | ( v3_pre_topc @ X42 @ X43 ) ) ),
    inference(simpl_trail,[status(thm)],['112','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
       != ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','120'])).

thf('122',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['109','121'])).

thf('123',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('127',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('129',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','69'])).

thf('130',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['128','129'])).

thf('131',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['127','130'])).

thf('132',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PSOATw9bS4
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:55:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.95/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.95/1.13  % Solved by: fo/fo7.sh
% 0.95/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.95/1.13  % done 2091 iterations in 0.662s
% 0.95/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.95/1.13  % SZS output start Refutation
% 0.95/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.95/1.13  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.95/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.95/1.13  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.95/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.95/1.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.95/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.95/1.13  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.95/1.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.95/1.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.95/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.95/1.13  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.95/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.95/1.13  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.95/1.13  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.95/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.95/1.13  thf(t76_tops_1, conjecture,
% 0.95/1.13    (![A:$i]:
% 0.95/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.95/1.13       ( ![B:$i]:
% 0.95/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.95/1.13           ( ( v3_pre_topc @ B @ A ) <=>
% 0.95/1.13             ( ( k2_tops_1 @ A @ B ) =
% 0.95/1.13               ( k7_subset_1 @
% 0.95/1.13                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.95/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.95/1.13    (~( ![A:$i]:
% 0.95/1.13        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.95/1.13          ( ![B:$i]:
% 0.95/1.13            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.95/1.13              ( ( v3_pre_topc @ B @ A ) <=>
% 0.95/1.13                ( ( k2_tops_1 @ A @ B ) =
% 0.95/1.13                  ( k7_subset_1 @
% 0.95/1.13                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.95/1.13    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.95/1.13  thf('0', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf(l78_tops_1, axiom,
% 0.95/1.13    (![A:$i]:
% 0.95/1.13     ( ( l1_pre_topc @ A ) =>
% 0.95/1.13       ( ![B:$i]:
% 0.95/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.95/1.13           ( ( k2_tops_1 @ A @ B ) =
% 0.95/1.13             ( k7_subset_1 @
% 0.95/1.13               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.95/1.13               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.95/1.13  thf('1', plain,
% 0.95/1.13      (![X38 : $i, X39 : $i]:
% 0.95/1.13         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.95/1.13          | ((k2_tops_1 @ X39 @ X38)
% 0.95/1.13              = (k7_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.95/1.13                 (k2_pre_topc @ X39 @ X38) @ (k1_tops_1 @ X39 @ X38)))
% 0.95/1.13          | ~ (l1_pre_topc @ X39))),
% 0.95/1.13      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.95/1.13  thf('2', plain,
% 0.95/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.95/1.13        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.95/1.13      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.13  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('4', plain,
% 0.95/1.13      (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.95/1.13      inference('demod', [status(thm)], ['2', '3'])).
% 0.95/1.13  thf('5', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf(dt_k2_pre_topc, axiom,
% 0.95/1.13    (![A:$i,B:$i]:
% 0.95/1.13     ( ( ( l1_pre_topc @ A ) & 
% 0.95/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.95/1.13       ( m1_subset_1 @
% 0.95/1.13         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.95/1.13  thf('6', plain,
% 0.95/1.13      (![X32 : $i, X33 : $i]:
% 0.95/1.13         (~ (l1_pre_topc @ X32)
% 0.95/1.13          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.95/1.13          | (m1_subset_1 @ (k2_pre_topc @ X32 @ X33) @ 
% 0.95/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.95/1.13      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.95/1.13  thf('7', plain,
% 0.95/1.13      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.95/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.95/1.13      inference('sup-', [status(thm)], ['5', '6'])).
% 0.95/1.13  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('9', plain,
% 0.95/1.13      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.95/1.13  thf(redefinition_k7_subset_1, axiom,
% 0.95/1.13    (![A:$i,B:$i,C:$i]:
% 0.95/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.95/1.13       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.95/1.13  thf('10', plain,
% 0.95/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.95/1.13         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.95/1.13          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.95/1.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.95/1.13  thf('11', plain,
% 0.95/1.13      (![X0 : $i]:
% 0.95/1.13         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['9', '10'])).
% 0.95/1.13  thf('12', plain,
% 0.95/1.13      (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.95/1.13      inference('demod', [status(thm)], ['4', '11'])).
% 0.95/1.13  thf(commutativity_k3_xboole_0, axiom,
% 0.95/1.13    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.95/1.13  thf('13', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.95/1.13  thf(t48_xboole_1, axiom,
% 0.95/1.13    (![A:$i,B:$i]:
% 0.95/1.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.95/1.13  thf('14', plain,
% 0.95/1.13      (![X8 : $i, X9 : $i]:
% 0.95/1.13         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.95/1.13           = (k3_xboole_0 @ X8 @ X9))),
% 0.95/1.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.95/1.13  thf(t36_xboole_1, axiom,
% 0.95/1.13    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.95/1.13  thf('15', plain,
% 0.95/1.13      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.95/1.13      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.95/1.13  thf(t3_subset, axiom,
% 0.95/1.13    (![A:$i,B:$i]:
% 0.95/1.13     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.95/1.13  thf('16', plain,
% 0.95/1.13      (![X26 : $i, X28 : $i]:
% 0.95/1.13         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 0.95/1.13      inference('cnf', [status(esa)], [t3_subset])).
% 0.95/1.13  thf('17', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['15', '16'])).
% 0.95/1.13  thf('18', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.95/1.13      inference('sup+', [status(thm)], ['14', '17'])).
% 0.95/1.13  thf('19', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.95/1.13      inference('sup+', [status(thm)], ['13', '18'])).
% 0.95/1.13  thf(involutiveness_k3_subset_1, axiom,
% 0.95/1.13    (![A:$i,B:$i]:
% 0.95/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.95/1.13       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.95/1.13  thf('20', plain,
% 0.95/1.13      (![X14 : $i, X15 : $i]:
% 0.95/1.13         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.95/1.13          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.95/1.13      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.95/1.13  thf('21', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.95/1.13           = (k3_xboole_0 @ X1 @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['19', '20'])).
% 0.95/1.13  thf('22', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.95/1.13  thf('23', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['15', '16'])).
% 0.95/1.13  thf('24', plain,
% 0.95/1.13      (![X14 : $i, X15 : $i]:
% 0.95/1.13         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.95/1.13          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.95/1.13      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.95/1.13  thf('25', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.95/1.13           = (k4_xboole_0 @ X0 @ X1))),
% 0.95/1.13      inference('sup-', [status(thm)], ['23', '24'])).
% 0.95/1.13  thf('26', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['15', '16'])).
% 0.95/1.13  thf(d5_subset_1, axiom,
% 0.95/1.13    (![A:$i,B:$i]:
% 0.95/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.95/1.13       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.95/1.13  thf('27', plain,
% 0.95/1.13      (![X10 : $i, X11 : $i]:
% 0.95/1.13         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.95/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.95/1.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.95/1.13  thf('28', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.95/1.13           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['26', '27'])).
% 0.95/1.13  thf('29', plain,
% 0.95/1.13      (![X8 : $i, X9 : $i]:
% 0.95/1.13         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.95/1.13           = (k3_xboole_0 @ X8 @ X9))),
% 0.95/1.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.95/1.13  thf('30', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.95/1.13           = (k3_xboole_0 @ X1 @ X0))),
% 0.95/1.13      inference('sup+', [status(thm)], ['28', '29'])).
% 0.95/1.13  thf('31', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.95/1.13           = (k4_xboole_0 @ X0 @ X1))),
% 0.95/1.13      inference('demod', [status(thm)], ['25', '30'])).
% 0.95/1.13  thf('32', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.95/1.13           = (k4_xboole_0 @ X0 @ X1))),
% 0.95/1.13      inference('sup+', [status(thm)], ['22', '31'])).
% 0.95/1.13  thf('33', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.95/1.13           = (k3_xboole_0 @ X1 @ X0))),
% 0.95/1.13      inference('demod', [status(thm)], ['21', '32'])).
% 0.95/1.13  thf('34', plain,
% 0.95/1.13      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.95/1.13         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.95/1.13            (k2_pre_topc @ sk_A @ sk_B)))),
% 0.95/1.13      inference('sup+', [status(thm)], ['12', '33'])).
% 0.95/1.13  thf('35', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf(t48_pre_topc, axiom,
% 0.95/1.13    (![A:$i]:
% 0.95/1.13     ( ( l1_pre_topc @ A ) =>
% 0.95/1.13       ( ![B:$i]:
% 0.95/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.95/1.13           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.95/1.13  thf('36', plain,
% 0.95/1.13      (![X34 : $i, X35 : $i]:
% 0.95/1.13         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.95/1.13          | (r1_tarski @ X34 @ (k2_pre_topc @ X35 @ X34))
% 0.95/1.13          | ~ (l1_pre_topc @ X35))),
% 0.95/1.13      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.95/1.13  thf('37', plain,
% 0.95/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.95/1.13        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['35', '36'])).
% 0.95/1.13  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('39', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.95/1.13      inference('demod', [status(thm)], ['37', '38'])).
% 0.95/1.13  thf('40', plain,
% 0.95/1.13      (![X26 : $i, X28 : $i]:
% 0.95/1.13         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 0.95/1.13      inference('cnf', [status(esa)], [t3_subset])).
% 0.95/1.13  thf('41', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['39', '40'])).
% 0.95/1.13  thf('42', plain,
% 0.95/1.13      (![X14 : $i, X15 : $i]:
% 0.95/1.13         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.95/1.13          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.95/1.13      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.95/1.13  thf('43', plain,
% 0.95/1.13      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.95/1.13      inference('sup-', [status(thm)], ['41', '42'])).
% 0.95/1.13  thf('44', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.95/1.13        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('45', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.95/1.13         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.95/1.13      inference('split', [status(esa)], ['44'])).
% 0.95/1.13  thf('46', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.95/1.13        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('47', plain,
% 0.95/1.13      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.95/1.13       ~
% 0.95/1.13       (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.95/1.13      inference('split', [status(esa)], ['46'])).
% 0.95/1.13  thf('48', plain,
% 0.95/1.13      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.95/1.13      inference('split', [status(esa)], ['44'])).
% 0.95/1.13  thf('49', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf(t55_tops_1, axiom,
% 0.95/1.13    (![A:$i]:
% 0.95/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.95/1.13       ( ![B:$i]:
% 0.95/1.13         ( ( l1_pre_topc @ B ) =>
% 0.95/1.13           ( ![C:$i]:
% 0.95/1.13             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.95/1.13               ( ![D:$i]:
% 0.95/1.13                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.95/1.13                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.95/1.13                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.95/1.13                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.95/1.13                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.95/1.13  thf('50', plain,
% 0.95/1.13      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.95/1.13         (~ (l1_pre_topc @ X40)
% 0.95/1.13          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.95/1.13          | ~ (v3_pre_topc @ X41 @ X40)
% 0.95/1.13          | ((k1_tops_1 @ X40 @ X41) = (X41))
% 0.95/1.13          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13          | ~ (l1_pre_topc @ X43)
% 0.95/1.13          | ~ (v2_pre_topc @ X43))),
% 0.95/1.13      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.95/1.13  thf('51', plain,
% 0.95/1.13      ((![X40 : $i, X41 : $i]:
% 0.95/1.13          (~ (l1_pre_topc @ X40)
% 0.95/1.13           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.95/1.13           | ~ (v3_pre_topc @ X41 @ X40)
% 0.95/1.13           | ((k1_tops_1 @ X40 @ X41) = (X41))))
% 0.95/1.13         <= ((![X40 : $i, X41 : $i]:
% 0.95/1.13                (~ (l1_pre_topc @ X40)
% 0.95/1.13                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.95/1.13                 | ~ (v3_pre_topc @ X41 @ X40)
% 0.95/1.13                 | ((k1_tops_1 @ X40 @ X41) = (X41)))))),
% 0.95/1.13      inference('split', [status(esa)], ['50'])).
% 0.95/1.13  thf('52', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('53', plain,
% 0.95/1.13      ((![X42 : $i, X43 : $i]:
% 0.95/1.13          (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13           | ~ (l1_pre_topc @ X43)
% 0.95/1.13           | ~ (v2_pre_topc @ X43)))
% 0.95/1.13         <= ((![X42 : $i, X43 : $i]:
% 0.95/1.13                (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13                 | ~ (l1_pre_topc @ X43)
% 0.95/1.13                 | ~ (v2_pre_topc @ X43))))),
% 0.95/1.13      inference('split', [status(esa)], ['50'])).
% 0.95/1.13  thf('54', plain,
% 0.95/1.13      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.95/1.13         <= ((![X42 : $i, X43 : $i]:
% 0.95/1.13                (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13                 | ~ (l1_pre_topc @ X43)
% 0.95/1.13                 | ~ (v2_pre_topc @ X43))))),
% 0.95/1.13      inference('sup-', [status(thm)], ['52', '53'])).
% 0.95/1.13  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('57', plain,
% 0.95/1.13      (~
% 0.95/1.13       (![X42 : $i, X43 : $i]:
% 0.95/1.13          (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13           | ~ (l1_pre_topc @ X43)
% 0.95/1.13           | ~ (v2_pre_topc @ X43)))),
% 0.95/1.13      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.95/1.13  thf('58', plain,
% 0.95/1.13      ((![X40 : $i, X41 : $i]:
% 0.95/1.13          (~ (l1_pre_topc @ X40)
% 0.95/1.13           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.95/1.13           | ~ (v3_pre_topc @ X41 @ X40)
% 0.95/1.13           | ((k1_tops_1 @ X40 @ X41) = (X41)))) | 
% 0.95/1.13       (![X42 : $i, X43 : $i]:
% 0.95/1.13          (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13           | ~ (l1_pre_topc @ X43)
% 0.95/1.13           | ~ (v2_pre_topc @ X43)))),
% 0.95/1.13      inference('split', [status(esa)], ['50'])).
% 0.95/1.13  thf('59', plain,
% 0.95/1.13      ((![X40 : $i, X41 : $i]:
% 0.95/1.13          (~ (l1_pre_topc @ X40)
% 0.95/1.13           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.95/1.13           | ~ (v3_pre_topc @ X41 @ X40)
% 0.95/1.13           | ((k1_tops_1 @ X40 @ X41) = (X41))))),
% 0.95/1.13      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.95/1.13  thf('60', plain,
% 0.95/1.13      (![X40 : $i, X41 : $i]:
% 0.95/1.13         (~ (l1_pre_topc @ X40)
% 0.95/1.13          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.95/1.13          | ~ (v3_pre_topc @ X41 @ X40)
% 0.95/1.13          | ((k1_tops_1 @ X40 @ X41) = (X41)))),
% 0.95/1.13      inference('simpl_trail', [status(thm)], ['51', '59'])).
% 0.95/1.13  thf('61', plain,
% 0.95/1.13      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.95/1.13        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.95/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.95/1.13      inference('sup-', [status(thm)], ['49', '60'])).
% 0.95/1.13  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('63', plain,
% 0.95/1.13      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.95/1.13      inference('demod', [status(thm)], ['61', '62'])).
% 0.95/1.13  thf('64', plain,
% 0.95/1.13      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.95/1.13         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['48', '63'])).
% 0.95/1.13  thf('65', plain,
% 0.95/1.13      (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.95/1.13      inference('demod', [status(thm)], ['2', '3'])).
% 0.95/1.13  thf('66', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.95/1.13         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.95/1.13      inference('sup+', [status(thm)], ['64', '65'])).
% 0.95/1.13  thf('67', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.95/1.13         <= (~
% 0.95/1.13             (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.95/1.13      inference('split', [status(esa)], ['46'])).
% 0.95/1.13  thf('68', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.95/1.13         <= (~
% 0.95/1.13             (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.95/1.13             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['66', '67'])).
% 0.95/1.13  thf('69', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.95/1.13       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.95/1.13      inference('simplify', [status(thm)], ['68'])).
% 0.95/1.13  thf('70', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.95/1.13       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.95/1.13      inference('split', [status(esa)], ['44'])).
% 0.95/1.13  thf('71', plain,
% 0.95/1.13      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.95/1.13      inference('sat_resolution*', [status(thm)], ['47', '69', '70'])).
% 0.95/1.13  thf('72', plain,
% 0.95/1.13      (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13            sk_B))),
% 0.95/1.13      inference('simpl_trail', [status(thm)], ['45', '71'])).
% 0.95/1.13  thf('73', plain,
% 0.95/1.13      (![X0 : $i]:
% 0.95/1.13         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.95/1.13           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['9', '10'])).
% 0.95/1.13  thf('74', plain,
% 0.95/1.13      (((k2_tops_1 @ sk_A @ sk_B)
% 0.95/1.13         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.95/1.13      inference('demod', [status(thm)], ['72', '73'])).
% 0.95/1.13  thf('75', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['39', '40'])).
% 0.95/1.13  thf('76', plain,
% 0.95/1.13      (![X10 : $i, X11 : $i]:
% 0.95/1.13         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.95/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.95/1.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.95/1.13  thf('77', plain,
% 0.95/1.13      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.95/1.13         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.95/1.13      inference('sup-', [status(thm)], ['75', '76'])).
% 0.95/1.13  thf('78', plain,
% 0.95/1.13      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.95/1.13         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.95/1.13      inference('sup+', [status(thm)], ['74', '77'])).
% 0.95/1.13  thf('79', plain,
% 0.95/1.13      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.95/1.13         = (sk_B))),
% 0.95/1.13      inference('demod', [status(thm)], ['43', '78'])).
% 0.95/1.13  thf('80', plain,
% 0.95/1.13      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.95/1.13         = (sk_B))),
% 0.95/1.13      inference('sup+', [status(thm)], ['34', '79'])).
% 0.95/1.13  thf('81', plain,
% 0.95/1.13      (![X8 : $i, X9 : $i]:
% 0.95/1.13         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.95/1.13           = (k3_xboole_0 @ X8 @ X9))),
% 0.95/1.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.95/1.13  thf('82', plain,
% 0.95/1.13      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.95/1.13      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.95/1.13  thf(d10_xboole_0, axiom,
% 0.95/1.13    (![A:$i,B:$i]:
% 0.95/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.95/1.13  thf('83', plain,
% 0.95/1.13      (![X2 : $i, X4 : $i]:
% 0.95/1.13         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.95/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.95/1.13  thf('84', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.95/1.13          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['82', '83'])).
% 0.95/1.13  thf('85', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.95/1.13          | ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.95/1.13      inference('sup-', [status(thm)], ['81', '84'])).
% 0.95/1.13  thf('86', plain,
% 0.95/1.13      (![X8 : $i, X9 : $i]:
% 0.95/1.13         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.95/1.13           = (k3_xboole_0 @ X8 @ X9))),
% 0.95/1.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.95/1.13  thf('87', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.95/1.13          | ((X1) = (k3_xboole_0 @ X1 @ X0)))),
% 0.95/1.13      inference('demod', [status(thm)], ['85', '86'])).
% 0.95/1.13  thf('88', plain,
% 0.95/1.13      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.95/1.13        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.95/1.13            = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.95/1.13               (k2_pre_topc @ sk_A @ sk_B))))),
% 0.95/1.13      inference('sup-', [status(thm)], ['80', '87'])).
% 0.95/1.13  thf('89', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf(t74_tops_1, axiom,
% 0.95/1.13    (![A:$i]:
% 0.95/1.13     ( ( l1_pre_topc @ A ) =>
% 0.95/1.13       ( ![B:$i]:
% 0.95/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.95/1.13           ( ( k1_tops_1 @ A @ B ) =
% 0.95/1.13             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.95/1.13  thf('90', plain,
% 0.95/1.13      (![X44 : $i, X45 : $i]:
% 0.95/1.13         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.95/1.13          | ((k1_tops_1 @ X45 @ X44)
% 0.95/1.13              = (k7_subset_1 @ (u1_struct_0 @ X45) @ X44 @ 
% 0.95/1.13                 (k2_tops_1 @ X45 @ X44)))
% 0.95/1.13          | ~ (l1_pre_topc @ X45))),
% 0.95/1.13      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.95/1.13  thf('91', plain,
% 0.95/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.95/1.13        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.95/1.13            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.95/1.13               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.95/1.13      inference('sup-', [status(thm)], ['89', '90'])).
% 0.95/1.13  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('93', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('94', plain,
% 0.95/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.95/1.13         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.95/1.13          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.95/1.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.95/1.13  thf('95', plain,
% 0.95/1.13      (![X0 : $i]:
% 0.95/1.13         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.95/1.13           = (k4_xboole_0 @ sk_B @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['93', '94'])).
% 0.95/1.13  thf('96', plain,
% 0.95/1.13      (((k1_tops_1 @ sk_A @ sk_B)
% 0.95/1.13         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.95/1.13      inference('demod', [status(thm)], ['91', '92', '95'])).
% 0.95/1.13  thf('97', plain,
% 0.95/1.13      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.95/1.13      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.95/1.13  thf('98', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.95/1.13      inference('sup+', [status(thm)], ['96', '97'])).
% 0.95/1.13  thf('99', plain,
% 0.95/1.13      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.95/1.13         = (sk_B))),
% 0.95/1.13      inference('sup+', [status(thm)], ['34', '79'])).
% 0.95/1.13  thf('100', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.95/1.13      inference('demod', [status(thm)], ['88', '98', '99'])).
% 0.95/1.13  thf('101', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf(dt_k3_subset_1, axiom,
% 0.95/1.13    (![A:$i,B:$i]:
% 0.95/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.95/1.13       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.95/1.13  thf('102', plain,
% 0.95/1.13      (![X12 : $i, X13 : $i]:
% 0.95/1.13         ((m1_subset_1 @ (k3_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.95/1.13          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.95/1.13      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.95/1.13  thf('103', plain,
% 0.95/1.13      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.95/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['101', '102'])).
% 0.95/1.13  thf('104', plain,
% 0.95/1.13      (![X10 : $i, X11 : $i]:
% 0.95/1.13         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.95/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.95/1.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.95/1.13  thf('105', plain,
% 0.95/1.13      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.95/1.13         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.95/1.13      inference('sup-', [status(thm)], ['103', '104'])).
% 0.95/1.13  thf('106', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('107', plain,
% 0.95/1.13      (![X14 : $i, X15 : $i]:
% 0.95/1.13         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.95/1.13          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.95/1.13      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.95/1.13  thf('108', plain,
% 0.95/1.13      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.95/1.13      inference('sup-', [status(thm)], ['106', '107'])).
% 0.95/1.13  thf('109', plain,
% 0.95/1.13      (((sk_B)
% 0.95/1.13         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.95/1.13      inference('demod', [status(thm)], ['105', '108'])).
% 0.95/1.13  thf('110', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['15', '16'])).
% 0.95/1.13  thf('111', plain,
% 0.95/1.13      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.95/1.13         (~ (l1_pre_topc @ X40)
% 0.95/1.13          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.95/1.13          | ((k1_tops_1 @ X43 @ X42) != (X42))
% 0.95/1.13          | (v3_pre_topc @ X42 @ X43)
% 0.95/1.13          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13          | ~ (l1_pre_topc @ X43)
% 0.95/1.13          | ~ (v2_pre_topc @ X43))),
% 0.95/1.13      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.95/1.13  thf('112', plain,
% 0.95/1.13      ((![X42 : $i, X43 : $i]:
% 0.95/1.13          (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13           | ~ (l1_pre_topc @ X43)
% 0.95/1.13           | ~ (v2_pre_topc @ X43)
% 0.95/1.13           | ((k1_tops_1 @ X43 @ X42) != (X42))
% 0.95/1.13           | (v3_pre_topc @ X42 @ X43)))
% 0.95/1.13         <= ((![X42 : $i, X43 : $i]:
% 0.95/1.13                (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13                 | ~ (l1_pre_topc @ X43)
% 0.95/1.13                 | ~ (v2_pre_topc @ X43)
% 0.95/1.13                 | ((k1_tops_1 @ X43 @ X42) != (X42))
% 0.95/1.13                 | (v3_pre_topc @ X42 @ X43))))),
% 0.95/1.13      inference('split', [status(esa)], ['111'])).
% 0.95/1.13  thf('113', plain,
% 0.95/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('114', plain,
% 0.95/1.13      ((![X40 : $i, X41 : $i]:
% 0.95/1.13          (~ (l1_pre_topc @ X40)
% 0.95/1.13           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))))
% 0.95/1.13         <= ((![X40 : $i, X41 : $i]:
% 0.95/1.13                (~ (l1_pre_topc @ X40)
% 0.95/1.13                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))))),
% 0.95/1.13      inference('split', [status(esa)], ['111'])).
% 0.95/1.13  thf('115', plain,
% 0.95/1.13      ((~ (l1_pre_topc @ sk_A))
% 0.95/1.13         <= ((![X40 : $i, X41 : $i]:
% 0.95/1.13                (~ (l1_pre_topc @ X40)
% 0.95/1.13                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))))),
% 0.95/1.13      inference('sup-', [status(thm)], ['113', '114'])).
% 0.95/1.13  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('117', plain,
% 0.95/1.13      (~
% 0.95/1.13       (![X40 : $i, X41 : $i]:
% 0.95/1.13          (~ (l1_pre_topc @ X40)
% 0.95/1.13           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))))),
% 0.95/1.13      inference('demod', [status(thm)], ['115', '116'])).
% 0.95/1.13  thf('118', plain,
% 0.95/1.13      ((![X42 : $i, X43 : $i]:
% 0.95/1.13          (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13           | ~ (l1_pre_topc @ X43)
% 0.95/1.13           | ~ (v2_pre_topc @ X43)
% 0.95/1.13           | ((k1_tops_1 @ X43 @ X42) != (X42))
% 0.95/1.13           | (v3_pre_topc @ X42 @ X43))) | 
% 0.95/1.13       (![X40 : $i, X41 : $i]:
% 0.95/1.13          (~ (l1_pre_topc @ X40)
% 0.95/1.13           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))))),
% 0.95/1.13      inference('split', [status(esa)], ['111'])).
% 0.95/1.13  thf('119', plain,
% 0.95/1.13      ((![X42 : $i, X43 : $i]:
% 0.95/1.13          (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13           | ~ (l1_pre_topc @ X43)
% 0.95/1.13           | ~ (v2_pre_topc @ X43)
% 0.95/1.13           | ((k1_tops_1 @ X43 @ X42) != (X42))
% 0.95/1.13           | (v3_pre_topc @ X42 @ X43)))),
% 0.95/1.13      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 0.95/1.13  thf('120', plain,
% 0.95/1.13      (![X42 : $i, X43 : $i]:
% 0.95/1.13         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.95/1.13          | ~ (l1_pre_topc @ X43)
% 0.95/1.13          | ~ (v2_pre_topc @ X43)
% 0.95/1.13          | ((k1_tops_1 @ X43 @ X42) != (X42))
% 0.95/1.13          | (v3_pre_topc @ X42 @ X43))),
% 0.95/1.13      inference('simpl_trail', [status(thm)], ['112', '119'])).
% 0.95/1.13  thf('121', plain,
% 0.95/1.13      (![X0 : $i, X1 : $i]:
% 0.95/1.13         ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.95/1.13          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.95/1.13              != (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.95/1.13          | ~ (v2_pre_topc @ X0)
% 0.95/1.13          | ~ (l1_pre_topc @ X0))),
% 0.95/1.13      inference('sup-', [status(thm)], ['110', '120'])).
% 0.95/1.13  thf('122', plain,
% 0.95/1.13      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.95/1.13          != (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.95/1.13        | ~ (l1_pre_topc @ sk_A)
% 0.95/1.13        | ~ (v2_pre_topc @ sk_A)
% 0.95/1.13        | (v3_pre_topc @ 
% 0.95/1.13           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.95/1.13           sk_A))),
% 0.95/1.13      inference('sup-', [status(thm)], ['109', '121'])).
% 0.95/1.13  thf('123', plain,
% 0.95/1.13      (((sk_B)
% 0.95/1.13         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.95/1.13      inference('demod', [status(thm)], ['105', '108'])).
% 0.95/1.13  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.95/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.13  thf('126', plain,
% 0.95/1.13      (((sk_B)
% 0.95/1.13         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.95/1.13            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.95/1.13      inference('demod', [status(thm)], ['105', '108'])).
% 0.95/1.13  thf('127', plain,
% 0.95/1.13      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 0.95/1.13      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.95/1.13  thf('128', plain,
% 0.95/1.13      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.95/1.13      inference('split', [status(esa)], ['46'])).
% 0.95/1.13  thf('129', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.95/1.13      inference('sat_resolution*', [status(thm)], ['47', '69'])).
% 0.95/1.13  thf('130', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.95/1.13      inference('simpl_trail', [status(thm)], ['128', '129'])).
% 0.95/1.13  thf('131', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 0.95/1.13      inference('clc', [status(thm)], ['127', '130'])).
% 0.95/1.13  thf('132', plain, ($false),
% 0.95/1.13      inference('simplify_reflect-', [status(thm)], ['100', '131'])).
% 0.95/1.13  
% 0.95/1.13  % SZS output end Refutation
% 0.95/1.13  
% 0.95/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
