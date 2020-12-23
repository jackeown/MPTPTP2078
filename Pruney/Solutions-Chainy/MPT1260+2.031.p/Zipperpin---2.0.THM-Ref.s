%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yNx6uhOiug

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:27 EST 2020

% Result     : Theorem 11.04s
% Output     : Refutation 11.04s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 924 expanded)
%              Number of leaves         :   43 ( 308 expanded)
%              Depth                    :   19
%              Number of atoms          : 1833 (9461 expanded)
%              Number of equality atoms :  140 ( 714 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( ( k2_tops_1 @ X55 @ X54 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X55 ) @ ( k2_pre_topc @ X55 @ X54 ) @ ( k1_tops_1 @ X55 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
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
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
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

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('21',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k1_tops_1 @ X51 @ X50 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['28','31'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('51',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['28','31'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('54',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('55',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('56',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','40','52','53','54','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('60',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X57 ) @ X56 ) @ X57 )
      | ( v4_pre_topc @ X56 @ X57 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('65',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('66',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('67',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

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

thf('70',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('75',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('76',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('77',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['57'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('84',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('86',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('89',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('93',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('94',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('95',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','96'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('98',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('99',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('100',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('101',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ ( k4_xboole_0 @ X30 @ X31 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) ) @ X31 ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('106',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('107',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('116',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k7_subset_1 @ X1 @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ ( k4_xboole_0 @ X30 @ X31 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) ) @ X31 ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('120',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','121'])).

thf('123',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('124',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['104','122','127'])).

thf('129',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['83','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('131',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k1_tops_1 @ X61 @ X60 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133','136'])).

thf('138',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['129','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('140',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X52 @ X53 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('141',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['138','144'])).

thf('146',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['79'])).

thf('147',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['57'])).

thf('149',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['80','147','148'])).

thf('150',plain,
    ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['78','149'])).

thf('151',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','150'])).

thf('152',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('153',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','153'])).

thf('155',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['79'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('157',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['80','147'])).

thf('159',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['157','158'])).

thf('160',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['154','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yNx6uhOiug
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:05:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 11.04/11.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.04/11.30  % Solved by: fo/fo7.sh
% 11.04/11.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.04/11.30  % done 8636 iterations in 10.838s
% 11.04/11.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.04/11.30  % SZS output start Refutation
% 11.04/11.30  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.04/11.30  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 11.04/11.30  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 11.04/11.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.04/11.30  thf(sk_B_type, type, sk_B: $i).
% 11.04/11.30  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 11.04/11.30  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.04/11.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.04/11.30  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 11.04/11.30  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 11.04/11.30  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 11.04/11.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.04/11.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.04/11.30  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 11.04/11.30  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 11.04/11.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 11.04/11.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.04/11.30  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 11.04/11.30  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 11.04/11.30  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 11.04/11.30  thf(sk_A_type, type, sk_A: $i).
% 11.04/11.30  thf(t76_tops_1, conjecture,
% 11.04/11.30    (![A:$i]:
% 11.04/11.30     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.04/11.30       ( ![B:$i]:
% 11.04/11.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.04/11.30           ( ( v3_pre_topc @ B @ A ) <=>
% 11.04/11.30             ( ( k2_tops_1 @ A @ B ) =
% 11.04/11.30               ( k7_subset_1 @
% 11.04/11.30                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 11.04/11.30  thf(zf_stmt_0, negated_conjecture,
% 11.04/11.30    (~( ![A:$i]:
% 11.04/11.30        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.04/11.30          ( ![B:$i]:
% 11.04/11.30            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.04/11.30              ( ( v3_pre_topc @ B @ A ) <=>
% 11.04/11.30                ( ( k2_tops_1 @ A @ B ) =
% 11.04/11.30                  ( k7_subset_1 @
% 11.04/11.30                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 11.04/11.30    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 11.04/11.30  thf('0', plain,
% 11.04/11.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf(l78_tops_1, axiom,
% 11.04/11.30    (![A:$i]:
% 11.04/11.30     ( ( l1_pre_topc @ A ) =>
% 11.04/11.30       ( ![B:$i]:
% 11.04/11.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.04/11.30           ( ( k2_tops_1 @ A @ B ) =
% 11.04/11.30             ( k7_subset_1 @
% 11.04/11.30               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 11.04/11.30               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 11.04/11.30  thf('1', plain,
% 11.04/11.30      (![X54 : $i, X55 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 11.04/11.30          | ((k2_tops_1 @ X55 @ X54)
% 11.04/11.30              = (k7_subset_1 @ (u1_struct_0 @ X55) @ 
% 11.04/11.30                 (k2_pre_topc @ X55 @ X54) @ (k1_tops_1 @ X55 @ X54)))
% 11.04/11.30          | ~ (l1_pre_topc @ X55))),
% 11.04/11.30      inference('cnf', [status(esa)], [l78_tops_1])).
% 11.04/11.30  thf('2', plain,
% 11.04/11.30      ((~ (l1_pre_topc @ sk_A)
% 11.04/11.30        | ((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 11.04/11.30      inference('sup-', [status(thm)], ['0', '1'])).
% 11.04/11.30  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('4', plain,
% 11.04/11.30      (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 11.04/11.30            (k1_tops_1 @ sk_A @ sk_B)))),
% 11.04/11.30      inference('demod', [status(thm)], ['2', '3'])).
% 11.04/11.30  thf('5', plain,
% 11.04/11.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf(dt_k2_pre_topc, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( ( l1_pre_topc @ A ) & 
% 11.04/11.30         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.04/11.30       ( m1_subset_1 @
% 11.04/11.30         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 11.04/11.30  thf('6', plain,
% 11.04/11.30      (![X46 : $i, X47 : $i]:
% 11.04/11.30         (~ (l1_pre_topc @ X46)
% 11.04/11.30          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 11.04/11.30          | (m1_subset_1 @ (k2_pre_topc @ X46 @ X47) @ 
% 11.04/11.30             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 11.04/11.30      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 11.04/11.30  thf('7', plain,
% 11.04/11.30      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 11.04/11.30         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.04/11.30        | ~ (l1_pre_topc @ sk_A))),
% 11.04/11.30      inference('sup-', [status(thm)], ['5', '6'])).
% 11.04/11.30  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('9', plain,
% 11.04/11.30      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 11.04/11.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('demod', [status(thm)], ['7', '8'])).
% 11.04/11.30  thf(redefinition_k7_subset_1, axiom,
% 11.04/11.30    (![A:$i,B:$i,C:$i]:
% 11.04/11.30     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.04/11.30       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 11.04/11.30  thf('10', plain,
% 11.04/11.30      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 11.04/11.30          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 11.04/11.30      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 11.04/11.30  thf('11', plain,
% 11.04/11.30      (![X0 : $i]:
% 11.04/11.30         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 11.04/11.30           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 11.04/11.30      inference('sup-', [status(thm)], ['9', '10'])).
% 11.04/11.30  thf('12', plain,
% 11.04/11.30      (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 11.04/11.30            (k1_tops_1 @ sk_A @ sk_B)))),
% 11.04/11.30      inference('demod', [status(thm)], ['4', '11'])).
% 11.04/11.30  thf('13', plain,
% 11.04/11.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf(d5_subset_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.04/11.30       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 11.04/11.30  thf('14', plain,
% 11.04/11.30      (![X34 : $i, X35 : $i]:
% 11.04/11.30         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 11.04/11.30          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 11.04/11.30      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.04/11.30  thf('15', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup-', [status(thm)], ['13', '14'])).
% 11.04/11.30  thf(t36_xboole_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 11.04/11.30  thf('16', plain,
% 11.04/11.30      (![X24 : $i, X25 : $i]: (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X24)),
% 11.04/11.30      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.04/11.30  thf(t3_subset, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.04/11.30  thf('17', plain,
% 11.04/11.30      (![X43 : $i, X45 : $i]:
% 11.04/11.30         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 11.04/11.30      inference('cnf', [status(esa)], [t3_subset])).
% 11.04/11.30  thf('18', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 11.04/11.30      inference('sup-', [status(thm)], ['16', '17'])).
% 11.04/11.30  thf('19', plain,
% 11.04/11.30      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 11.04/11.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['15', '18'])).
% 11.04/11.30  thf(dt_k3_subset_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.04/11.30       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 11.04/11.30  thf('20', plain,
% 11.04/11.30      (![X36 : $i, X37 : $i]:
% 11.04/11.30         ((m1_subset_1 @ (k3_subset_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36))
% 11.04/11.30          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 11.04/11.30      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 11.04/11.30  thf('21', plain,
% 11.04/11.30      ((m1_subset_1 @ 
% 11.04/11.30        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 11.04/11.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('sup-', [status(thm)], ['19', '20'])).
% 11.04/11.30  thf(d1_tops_1, axiom,
% 11.04/11.30    (![A:$i]:
% 11.04/11.30     ( ( l1_pre_topc @ A ) =>
% 11.04/11.30       ( ![B:$i]:
% 11.04/11.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.04/11.30           ( ( k1_tops_1 @ A @ B ) =
% 11.04/11.30             ( k3_subset_1 @
% 11.04/11.30               ( u1_struct_0 @ A ) @ 
% 11.04/11.30               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 11.04/11.30  thf('22', plain,
% 11.04/11.30      (![X50 : $i, X51 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 11.04/11.30          | ((k1_tops_1 @ X51 @ X50)
% 11.04/11.30              = (k3_subset_1 @ (u1_struct_0 @ X51) @ 
% 11.04/11.30                 (k2_pre_topc @ X51 @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50))))
% 11.04/11.30          | ~ (l1_pre_topc @ X51))),
% 11.04/11.30      inference('cnf', [status(esa)], [d1_tops_1])).
% 11.04/11.30  thf('23', plain,
% 11.04/11.30      ((~ (l1_pre_topc @ sk_A)
% 11.04/11.30        | ((k1_tops_1 @ sk_A @ 
% 11.04/11.30            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 11.04/11.30            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30               (k2_pre_topc @ sk_A @ 
% 11.04/11.30                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))))),
% 11.04/11.30      inference('sup-', [status(thm)], ['21', '22'])).
% 11.04/11.30  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('25', plain,
% 11.04/11.30      (((k1_tops_1 @ sk_A @ 
% 11.04/11.30         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 11.04/11.30         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30            (k2_pre_topc @ sk_A @ 
% 11.04/11.30             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 11.04/11.30      inference('demod', [status(thm)], ['23', '24'])).
% 11.04/11.30  thf('26', plain,
% 11.04/11.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('27', plain,
% 11.04/11.30      (![X43 : $i, X44 : $i]:
% 11.04/11.30         ((r1_tarski @ X43 @ X44) | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 11.04/11.30      inference('cnf', [status(esa)], [t3_subset])).
% 11.04/11.30  thf('28', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.04/11.30      inference('sup-', [status(thm)], ['26', '27'])).
% 11.04/11.30  thf(t28_xboole_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 11.04/11.30  thf('29', plain,
% 11.04/11.30      (![X21 : $i, X22 : $i]:
% 11.04/11.30         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 11.04/11.30      inference('cnf', [status(esa)], [t28_xboole_1])).
% 11.04/11.30  thf(t12_setfam_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.04/11.30  thf('30', plain,
% 11.04/11.30      (![X41 : $i, X42 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 11.04/11.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.04/11.30  thf('31', plain,
% 11.04/11.30      (![X21 : $i, X22 : $i]:
% 11.04/11.30         (((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (X21))
% 11.04/11.30          | ~ (r1_tarski @ X21 @ X22))),
% 11.04/11.30      inference('demod', [status(thm)], ['29', '30'])).
% 11.04/11.30  thf('32', plain,
% 11.04/11.30      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 11.04/11.30      inference('sup-', [status(thm)], ['28', '31'])).
% 11.04/11.30  thf(commutativity_k2_tarski, axiom,
% 11.04/11.30    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 11.04/11.30  thf('33', plain,
% 11.04/11.30      (![X32 : $i, X33 : $i]:
% 11.04/11.30         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 11.04/11.30      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 11.04/11.30  thf(t100_xboole_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 11.04/11.30  thf('34', plain,
% 11.04/11.30      (![X13 : $i, X14 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X13 @ X14)
% 11.04/11.30           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 11.04/11.30      inference('cnf', [status(esa)], [t100_xboole_1])).
% 11.04/11.30  thf('35', plain,
% 11.04/11.30      (![X41 : $i, X42 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 11.04/11.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.04/11.30  thf('36', plain,
% 11.04/11.30      (![X13 : $i, X14 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X13 @ X14)
% 11.04/11.30           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 11.04/11.30      inference('demod', [status(thm)], ['34', '35'])).
% 11.04/11.30  thf('37', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X0 @ X1)
% 11.04/11.30           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 11.04/11.30      inference('sup+', [status(thm)], ['33', '36'])).
% 11.04/11.30  thf('38', plain,
% 11.04/11.30      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['32', '37'])).
% 11.04/11.30  thf('39', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup-', [status(thm)], ['13', '14'])).
% 11.04/11.30  thf('40', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('41', plain,
% 11.04/11.30      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['32', '37'])).
% 11.04/11.30  thf('42', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 11.04/11.30      inference('sup-', [status(thm)], ['16', '17'])).
% 11.04/11.30  thf('43', plain,
% 11.04/11.30      (![X34 : $i, X35 : $i]:
% 11.04/11.30         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 11.04/11.30          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 11.04/11.30      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.04/11.30  thf('44', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 11.04/11.30           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 11.04/11.30      inference('sup-', [status(thm)], ['42', '43'])).
% 11.04/11.30  thf(t48_xboole_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.04/11.30  thf('45', plain,
% 11.04/11.30      (![X27 : $i, X28 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 11.04/11.30           = (k3_xboole_0 @ X27 @ X28))),
% 11.04/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.04/11.30  thf('46', plain,
% 11.04/11.30      (![X41 : $i, X42 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 11.04/11.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.04/11.30  thf('47', plain,
% 11.04/11.30      (![X27 : $i, X28 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X27 @ X28)))),
% 11.04/11.30      inference('demod', [status(thm)], ['45', '46'])).
% 11.04/11.30  thf('48', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['44', '47'])).
% 11.04/11.30  thf('49', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30         = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['41', '48'])).
% 11.04/11.30  thf('50', plain,
% 11.04/11.30      (![X32 : $i, X33 : $i]:
% 11.04/11.30         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 11.04/11.30      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 11.04/11.30  thf('51', plain,
% 11.04/11.30      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 11.04/11.30      inference('sup-', [status(thm)], ['28', '31'])).
% 11.04/11.30  thf('52', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 11.04/11.30      inference('demod', [status(thm)], ['49', '50', '51'])).
% 11.04/11.30  thf('53', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('54', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 11.04/11.30      inference('demod', [status(thm)], ['49', '50', '51'])).
% 11.04/11.30  thf('55', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('56', plain,
% 11.04/11.30      (((k1_tops_1 @ sk_A @ sk_B)
% 11.04/11.30         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 11.04/11.30      inference('demod', [status(thm)], ['25', '40', '52', '53', '54', '55'])).
% 11.04/11.30  thf('57', plain,
% 11.04/11.30      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 11.04/11.30        | (v3_pre_topc @ sk_B @ sk_A))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('58', plain,
% 11.04/11.30      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 11.04/11.30      inference('split', [status(esa)], ['57'])).
% 11.04/11.30  thf('59', plain,
% 11.04/11.30      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 11.04/11.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['15', '18'])).
% 11.04/11.30  thf(t29_tops_1, axiom,
% 11.04/11.30    (![A:$i]:
% 11.04/11.30     ( ( l1_pre_topc @ A ) =>
% 11.04/11.30       ( ![B:$i]:
% 11.04/11.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.04/11.30           ( ( v4_pre_topc @ B @ A ) <=>
% 11.04/11.30             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 11.04/11.30  thf('60', plain,
% 11.04/11.30      (![X56 : $i, X57 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 11.04/11.30          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X57) @ X56) @ X57)
% 11.04/11.30          | (v4_pre_topc @ X56 @ X57)
% 11.04/11.30          | ~ (l1_pre_topc @ X57))),
% 11.04/11.30      inference('cnf', [status(esa)], [t29_tops_1])).
% 11.04/11.30  thf('61', plain,
% 11.04/11.30      ((~ (l1_pre_topc @ sk_A)
% 11.04/11.30        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 11.04/11.30        | ~ (v3_pre_topc @ 
% 11.04/11.30             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 11.04/11.30             sk_A))),
% 11.04/11.30      inference('sup-', [status(thm)], ['59', '60'])).
% 11.04/11.30  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('63', plain,
% 11.04/11.30      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 11.04/11.30        | ~ (v3_pre_topc @ 
% 11.04/11.30             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 11.04/11.30             sk_A))),
% 11.04/11.30      inference('demod', [status(thm)], ['61', '62'])).
% 11.04/11.30  thf('64', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('65', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('66', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 11.04/11.30      inference('demod', [status(thm)], ['49', '50', '51'])).
% 11.04/11.30  thf('67', plain,
% 11.04/11.30      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 11.04/11.30        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 11.04/11.30      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 11.04/11.30  thf('68', plain,
% 11.04/11.30      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 11.04/11.30         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 11.04/11.30      inference('sup-', [status(thm)], ['58', '67'])).
% 11.04/11.30  thf('69', plain,
% 11.04/11.30      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 11.04/11.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['15', '18'])).
% 11.04/11.30  thf(t52_pre_topc, axiom,
% 11.04/11.30    (![A:$i]:
% 11.04/11.30     ( ( l1_pre_topc @ A ) =>
% 11.04/11.30       ( ![B:$i]:
% 11.04/11.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.04/11.30           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 11.04/11.30             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 11.04/11.30               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 11.04/11.30  thf('70', plain,
% 11.04/11.30      (![X48 : $i, X49 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 11.04/11.30          | ~ (v4_pre_topc @ X48 @ X49)
% 11.04/11.30          | ((k2_pre_topc @ X49 @ X48) = (X48))
% 11.04/11.30          | ~ (l1_pre_topc @ X49))),
% 11.04/11.30      inference('cnf', [status(esa)], [t52_pre_topc])).
% 11.04/11.30  thf('71', plain,
% 11.04/11.30      ((~ (l1_pre_topc @ sk_A)
% 11.04/11.30        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 11.04/11.30      inference('sup-', [status(thm)], ['69', '70'])).
% 11.04/11.30  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('73', plain,
% 11.04/11.30      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 11.04/11.30      inference('demod', [status(thm)], ['71', '72'])).
% 11.04/11.30  thf('74', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('75', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('76', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.04/11.30  thf('77', plain,
% 11.04/11.30      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30        | ~ (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 11.04/11.30      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 11.04/11.30  thf('78', plain,
% 11.04/11.30      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 11.04/11.30         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 11.04/11.30      inference('sup-', [status(thm)], ['68', '77'])).
% 11.04/11.30  thf('79', plain,
% 11.04/11.30      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 11.04/11.30        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('80', plain,
% 11.04/11.30      (~
% 11.04/11.30       (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 11.04/11.30       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 11.04/11.30      inference('split', [status(esa)], ['79'])).
% 11.04/11.30  thf('81', plain,
% 11.04/11.30      (![X0 : $i]:
% 11.04/11.30         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 11.04/11.30           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 11.04/11.30      inference('sup-', [status(thm)], ['9', '10'])).
% 11.04/11.30  thf('82', plain,
% 11.04/11.30      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 11.04/11.30         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 11.04/11.30      inference('split', [status(esa)], ['57'])).
% 11.04/11.30  thf('83', plain,
% 11.04/11.30      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 11.04/11.30         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 11.04/11.30      inference('sup+', [status(thm)], ['81', '82'])).
% 11.04/11.30  thf(idempotence_k3_xboole_0, axiom,
% 11.04/11.30    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 11.04/11.30  thf('84', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 11.04/11.30      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 11.04/11.30  thf('85', plain,
% 11.04/11.30      (![X41 : $i, X42 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 11.04/11.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.04/11.30  thf('86', plain,
% 11.04/11.30      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 11.04/11.30      inference('demod', [status(thm)], ['84', '85'])).
% 11.04/11.30  thf('87', plain,
% 11.04/11.30      (![X13 : $i, X14 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X13 @ X14)
% 11.04/11.30           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 11.04/11.30      inference('demod', [status(thm)], ['34', '35'])).
% 11.04/11.30  thf('88', plain,
% 11.04/11.30      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 11.04/11.30      inference('sup+', [status(thm)], ['86', '87'])).
% 11.04/11.30  thf(t3_boole, axiom,
% 11.04/11.30    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 11.04/11.30  thf('89', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 11.04/11.30      inference('cnf', [status(esa)], [t3_boole])).
% 11.04/11.30  thf('90', plain,
% 11.04/11.30      (![X27 : $i, X28 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X27 @ X28)))),
% 11.04/11.30      inference('demod', [status(thm)], ['45', '46'])).
% 11.04/11.30  thf('91', plain,
% 11.04/11.30      (![X0 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X0 @ X0)
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['89', '90'])).
% 11.04/11.30  thf('92', plain,
% 11.04/11.30      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 11.04/11.30      inference('sup+', [status(thm)], ['86', '87'])).
% 11.04/11.30  thf(t2_boole, axiom,
% 11.04/11.30    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 11.04/11.30  thf('93', plain,
% 11.04/11.30      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 11.04/11.30      inference('cnf', [status(esa)], [t2_boole])).
% 11.04/11.30  thf('94', plain,
% 11.04/11.30      (![X41 : $i, X42 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 11.04/11.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.04/11.30  thf('95', plain,
% 11.04/11.30      (![X23 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 11.04/11.30      inference('demod', [status(thm)], ['93', '94'])).
% 11.04/11.30  thf('96', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 11.04/11.30      inference('demod', [status(thm)], ['91', '92', '95'])).
% 11.04/11.30  thf('97', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 11.04/11.30      inference('demod', [status(thm)], ['88', '96'])).
% 11.04/11.30  thf(t49_xboole_1, axiom,
% 11.04/11.30    (![A:$i,B:$i,C:$i]:
% 11.04/11.30     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 11.04/11.30       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 11.04/11.30  thf('98', plain,
% 11.04/11.30      (![X29 : $i, X30 : $i, X31 : $i]:
% 11.04/11.30         ((k3_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X31))
% 11.04/11.30           = (k4_xboole_0 @ (k3_xboole_0 @ X29 @ X30) @ X31))),
% 11.04/11.30      inference('cnf', [status(esa)], [t49_xboole_1])).
% 11.04/11.30  thf('99', plain,
% 11.04/11.30      (![X41 : $i, X42 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 11.04/11.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.04/11.30  thf('100', plain,
% 11.04/11.30      (![X41 : $i, X42 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 11.04/11.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.04/11.30  thf('101', plain,
% 11.04/11.30      (![X29 : $i, X30 : $i, X31 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X29 @ (k4_xboole_0 @ X30 @ X31)))
% 11.04/11.30           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X29 @ X30)) @ X31))),
% 11.04/11.30      inference('demod', [status(thm)], ['98', '99', '100'])).
% 11.04/11.30  thf('102', plain,
% 11.04/11.30      (![X13 : $i, X14 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X13 @ X14)
% 11.04/11.30           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 11.04/11.30      inference('demod', [status(thm)], ['34', '35'])).
% 11.04/11.30  thf('103', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 11.04/11.30           = (k5_xboole_0 @ X2 @ 
% 11.04/11.30              (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['101', '102'])).
% 11.04/11.30  thf('104', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X1 @ 
% 11.04/11.30           (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 11.04/11.30           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 11.04/11.30      inference('sup+', [status(thm)], ['97', '103'])).
% 11.04/11.30  thf('105', plain,
% 11.04/11.30      (![X32 : $i, X33 : $i]:
% 11.04/11.30         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 11.04/11.30      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 11.04/11.30  thf('106', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 11.04/11.30      inference('cnf', [status(esa)], [t3_boole])).
% 11.04/11.30  thf('107', plain,
% 11.04/11.30      (![X24 : $i, X25 : $i]: (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X24)),
% 11.04/11.30      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.04/11.30  thf('108', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 11.04/11.30      inference('sup+', [status(thm)], ['106', '107'])).
% 11.04/11.30  thf('109', plain,
% 11.04/11.30      (![X43 : $i, X45 : $i]:
% 11.04/11.30         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 11.04/11.30      inference('cnf', [status(esa)], [t3_subset])).
% 11.04/11.30  thf('110', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.04/11.30      inference('sup-', [status(thm)], ['108', '109'])).
% 11.04/11.30  thf('111', plain,
% 11.04/11.30      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 11.04/11.30          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 11.04/11.30      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 11.04/11.30  thf('112', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 11.04/11.30      inference('sup-', [status(thm)], ['110', '111'])).
% 11.04/11.30  thf('113', plain,
% 11.04/11.30      (![X27 : $i, X28 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X27 @ X28)))),
% 11.04/11.30      inference('demod', [status(thm)], ['45', '46'])).
% 11.04/11.30  thf('114', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k7_subset_1 @ X1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['112', '113'])).
% 11.04/11.30  thf('115', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 11.04/11.30      inference('sup-', [status(thm)], ['110', '111'])).
% 11.04/11.30  thf('116', plain,
% 11.04/11.30      (![X27 : $i, X28 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X27 @ X28)))),
% 11.04/11.30      inference('demod', [status(thm)], ['45', '46'])).
% 11.04/11.30  thf('117', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X1 @ (k7_subset_1 @ X1 @ X1 @ X0))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 11.04/11.30      inference('sup+', [status(thm)], ['115', '116'])).
% 11.04/11.30  thf('118', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 11.04/11.30           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 11.04/11.30      inference('sup+', [status(thm)], ['114', '117'])).
% 11.04/11.30  thf('119', plain,
% 11.04/11.30      (![X29 : $i, X30 : $i, X31 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X29 @ (k4_xboole_0 @ X30 @ X31)))
% 11.04/11.30           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X29 @ X30)) @ X31))),
% 11.04/11.30      inference('demod', [status(thm)], ['98', '99', '100'])).
% 11.04/11.30  thf('120', plain,
% 11.04/11.30      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 11.04/11.30      inference('demod', [status(thm)], ['84', '85'])).
% 11.04/11.30  thf('121', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 11.04/11.30           = (k4_xboole_0 @ X1 @ X0))),
% 11.04/11.30      inference('demod', [status(thm)], ['118', '119', '120'])).
% 11.04/11.30  thf('122', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 11.04/11.30           = (k4_xboole_0 @ X0 @ X1))),
% 11.04/11.30      inference('sup+', [status(thm)], ['105', '121'])).
% 11.04/11.30  thf('123', plain,
% 11.04/11.30      (![X23 : $i]:
% 11.04/11.30         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 11.04/11.30      inference('demod', [status(thm)], ['93', '94'])).
% 11.04/11.30  thf('124', plain,
% 11.04/11.30      (![X13 : $i, X14 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X13 @ X14)
% 11.04/11.30           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 11.04/11.30      inference('demod', [status(thm)], ['34', '35'])).
% 11.04/11.30  thf('125', plain,
% 11.04/11.30      (![X0 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 11.04/11.30      inference('sup+', [status(thm)], ['123', '124'])).
% 11.04/11.30  thf('126', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 11.04/11.30      inference('cnf', [status(esa)], [t3_boole])).
% 11.04/11.30  thf('127', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 11.04/11.30      inference('sup+', [status(thm)], ['125', '126'])).
% 11.04/11.30  thf('128', plain,
% 11.04/11.30      (![X0 : $i, X1 : $i]:
% 11.04/11.30         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 11.04/11.30      inference('demod', [status(thm)], ['104', '122', '127'])).
% 11.04/11.30  thf('129', plain,
% 11.04/11.30      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 11.04/11.30         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 11.04/11.30      inference('sup+', [status(thm)], ['83', '128'])).
% 11.04/11.30  thf('130', plain,
% 11.04/11.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf(t74_tops_1, axiom,
% 11.04/11.30    (![A:$i]:
% 11.04/11.30     ( ( l1_pre_topc @ A ) =>
% 11.04/11.30       ( ![B:$i]:
% 11.04/11.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.04/11.30           ( ( k1_tops_1 @ A @ B ) =
% 11.04/11.30             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 11.04/11.30  thf('131', plain,
% 11.04/11.30      (![X60 : $i, X61 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 11.04/11.30          | ((k1_tops_1 @ X61 @ X60)
% 11.04/11.30              = (k7_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 11.04/11.30                 (k2_tops_1 @ X61 @ X60)))
% 11.04/11.30          | ~ (l1_pre_topc @ X61))),
% 11.04/11.30      inference('cnf', [status(esa)], [t74_tops_1])).
% 11.04/11.30  thf('132', plain,
% 11.04/11.30      ((~ (l1_pre_topc @ sk_A)
% 11.04/11.30        | ((k1_tops_1 @ sk_A @ sk_B)
% 11.04/11.30            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.04/11.30               (k2_tops_1 @ sk_A @ sk_B))))),
% 11.04/11.30      inference('sup-', [status(thm)], ['130', '131'])).
% 11.04/11.30  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('134', plain,
% 11.04/11.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('135', plain,
% 11.04/11.30      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.04/11.30         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 11.04/11.30          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 11.04/11.30      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 11.04/11.30  thf('136', plain,
% 11.04/11.30      (![X0 : $i]:
% 11.04/11.30         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 11.04/11.30           = (k4_xboole_0 @ sk_B @ X0))),
% 11.04/11.30      inference('sup-', [status(thm)], ['134', '135'])).
% 11.04/11.30  thf('137', plain,
% 11.04/11.30      (((k1_tops_1 @ sk_A @ sk_B)
% 11.04/11.30         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 11.04/11.30      inference('demod', [status(thm)], ['132', '133', '136'])).
% 11.04/11.30  thf('138', plain,
% 11.04/11.30      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 11.04/11.30         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 11.04/11.30      inference('sup+', [status(thm)], ['129', '137'])).
% 11.04/11.30  thf('139', plain,
% 11.04/11.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf(fc9_tops_1, axiom,
% 11.04/11.30    (![A:$i,B:$i]:
% 11.04/11.30     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 11.04/11.30         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.04/11.30       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 11.04/11.30  thf('140', plain,
% 11.04/11.30      (![X52 : $i, X53 : $i]:
% 11.04/11.30         (~ (l1_pre_topc @ X52)
% 11.04/11.30          | ~ (v2_pre_topc @ X52)
% 11.04/11.30          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 11.04/11.30          | (v3_pre_topc @ (k1_tops_1 @ X52 @ X53) @ X52))),
% 11.04/11.30      inference('cnf', [status(esa)], [fc9_tops_1])).
% 11.04/11.30  thf('141', plain,
% 11.04/11.30      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 11.04/11.30        | ~ (v2_pre_topc @ sk_A)
% 11.04/11.30        | ~ (l1_pre_topc @ sk_A))),
% 11.04/11.30      inference('sup-', [status(thm)], ['139', '140'])).
% 11.04/11.30  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 11.04/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.30  thf('144', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 11.04/11.30      inference('demod', [status(thm)], ['141', '142', '143'])).
% 11.04/11.30  thf('145', plain,
% 11.04/11.30      (((v3_pre_topc @ sk_B @ sk_A))
% 11.04/11.30         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 11.04/11.30      inference('sup+', [status(thm)], ['138', '144'])).
% 11.04/11.30  thf('146', plain,
% 11.04/11.30      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 11.04/11.30      inference('split', [status(esa)], ['79'])).
% 11.04/11.30  thf('147', plain,
% 11.04/11.30      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 11.04/11.30       ~
% 11.04/11.30       (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 11.04/11.30      inference('sup-', [status(thm)], ['145', '146'])).
% 11.04/11.30  thf('148', plain,
% 11.04/11.30      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 11.04/11.30       (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 11.04/11.30      inference('split', [status(esa)], ['57'])).
% 11.04/11.30  thf('149', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 11.04/11.30      inference('sat_resolution*', [status(thm)], ['80', '147', '148'])).
% 11.04/11.30  thf('150', plain,
% 11.04/11.30      (((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.04/11.30         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.04/11.30      inference('simpl_trail', [status(thm)], ['78', '149'])).
% 11.04/11.30  thf('151', plain,
% 11.04/11.30      (((k1_tops_1 @ sk_A @ sk_B)
% 11.04/11.30         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 11.04/11.30      inference('demod', [status(thm)], ['56', '150'])).
% 11.04/11.30  thf('152', plain,
% 11.04/11.30      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 11.04/11.30      inference('demod', [status(thm)], ['49', '50', '51'])).
% 11.04/11.30  thf('153', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 11.04/11.30      inference('sup+', [status(thm)], ['151', '152'])).
% 11.04/11.30  thf('154', plain,
% 11.04/11.30      (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 11.04/11.30      inference('demod', [status(thm)], ['12', '153'])).
% 11.04/11.30  thf('155', plain,
% 11.04/11.30      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 11.04/11.30         <= (~
% 11.04/11.30             (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 11.04/11.30      inference('split', [status(esa)], ['79'])).
% 11.04/11.30  thf('156', plain,
% 11.04/11.30      (![X0 : $i]:
% 11.04/11.30         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 11.04/11.30           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 11.04/11.30      inference('sup-', [status(thm)], ['9', '10'])).
% 11.04/11.30  thf('157', plain,
% 11.04/11.30      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 11.04/11.30         <= (~
% 11.04/11.30             (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 11.04/11.30      inference('demod', [status(thm)], ['155', '156'])).
% 11.04/11.30  thf('158', plain,
% 11.04/11.30      (~
% 11.04/11.30       (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.04/11.30             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 11.04/11.30      inference('sat_resolution*', [status(thm)], ['80', '147'])).
% 11.04/11.30  thf('159', plain,
% 11.04/11.30      (((k2_tops_1 @ sk_A @ sk_B)
% 11.04/11.30         != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 11.04/11.30      inference('simpl_trail', [status(thm)], ['157', '158'])).
% 11.04/11.30  thf('160', plain, ($false),
% 11.04/11.30      inference('simplify_reflect-', [status(thm)], ['154', '159'])).
% 11.04/11.30  
% 11.04/11.30  % SZS output end Refutation
% 11.04/11.30  
% 11.04/11.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
