%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ZPlthb8x9

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:27 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 380 expanded)
%              Number of leaves         :   44 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          : 1545 (4324 expanded)
%              Number of equality atoms :  108 ( 293 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ X44 @ X45 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf('26',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v4_pre_topc @ X36 @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('37',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ X38 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ ( k3_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 ) ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X25 @ ( k3_subset_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('50',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ X42 ) @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('65',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('67',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('69',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('74',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['70'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('80',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k7_subset_1 @ X27 @ X26 @ X28 )
        = ( k4_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('86',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','88'])).

thf('90',plain,
    ( ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','89'])).

thf('91',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('94',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('95',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('96',plain,(
    ! [X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('103',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k1_tops_1 @ X47 @ X46 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X47 ) @ X46 @ ( k2_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k7_subset_1 @ X27 @ X26 @ X28 )
        = ( k4_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','108'])).

thf('110',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['101','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('112',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X40 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('113',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['110','116'])).

thf('118',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('119',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','62','63','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ZPlthb8x9
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.35/1.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.54  % Solved by: fo/fo7.sh
% 1.35/1.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.54  % done 1448 iterations in 1.087s
% 1.35/1.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.54  % SZS output start Refutation
% 1.35/1.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.35/1.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.35/1.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.35/1.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.35/1.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.35/1.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.35/1.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.35/1.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.35/1.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.35/1.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.35/1.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.35/1.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.35/1.54  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.35/1.54  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.35/1.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.35/1.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.35/1.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.35/1.54  thf(t76_tops_1, conjecture,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.35/1.54       ( ![B:$i]:
% 1.35/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.35/1.54           ( ( v3_pre_topc @ B @ A ) <=>
% 1.35/1.54             ( ( k2_tops_1 @ A @ B ) =
% 1.35/1.54               ( k7_subset_1 @
% 1.35/1.54                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.35/1.54  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.54    (~( ![A:$i]:
% 1.35/1.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.35/1.54          ( ![B:$i]:
% 1.35/1.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.35/1.54              ( ( v3_pre_topc @ B @ A ) <=>
% 1.35/1.54                ( ( k2_tops_1 @ A @ B ) =
% 1.35/1.54                  ( k7_subset_1 @
% 1.35/1.54                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.35/1.54    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.35/1.54  thf('0', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.35/1.54        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('1', plain,
% 1.35/1.54      (~
% 1.35/1.54       (((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.35/1.54       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('split', [status(esa)], ['0'])).
% 1.35/1.54  thf('2', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.35/1.54        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('3', plain,
% 1.35/1.54      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('split', [status(esa)], ['2'])).
% 1.35/1.54  thf('4', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(t30_tops_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( l1_pre_topc @ A ) =>
% 1.35/1.54       ( ![B:$i]:
% 1.35/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.35/1.54           ( ( v3_pre_topc @ B @ A ) <=>
% 1.35/1.54             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.35/1.54  thf('5', plain,
% 1.35/1.54      (![X44 : $i, X45 : $i]:
% 1.35/1.54         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.35/1.54          | ~ (v3_pre_topc @ X44 @ X45)
% 1.35/1.54          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 1.35/1.54          | ~ (l1_pre_topc @ X45))),
% 1.35/1.54      inference('cnf', [status(esa)], [t30_tops_1])).
% 1.35/1.54  thf('6', plain,
% 1.35/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.35/1.54        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.35/1.54        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['4', '5'])).
% 1.35/1.54  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('8', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(t3_subset, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.35/1.54  thf('9', plain,
% 1.35/1.54      (![X31 : $i, X32 : $i]:
% 1.35/1.54         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 1.35/1.54      inference('cnf', [status(esa)], [t3_subset])).
% 1.35/1.54  thf('10', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['8', '9'])).
% 1.35/1.54  thf(t28_xboole_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.35/1.54  thf('11', plain,
% 1.35/1.54      (![X14 : $i, X15 : $i]:
% 1.35/1.54         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.35/1.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.54  thf(t12_setfam_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.35/1.54  thf('12', plain,
% 1.35/1.54      (![X29 : $i, X30 : $i]:
% 1.35/1.54         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 1.35/1.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.35/1.54  thf('13', plain,
% 1.35/1.54      (![X14 : $i, X15 : $i]:
% 1.35/1.54         (((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (X14))
% 1.35/1.54          | ~ (r1_tarski @ X14 @ X15))),
% 1.35/1.54      inference('demod', [status(thm)], ['11', '12'])).
% 1.35/1.54  thf('14', plain,
% 1.35/1.54      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 1.35/1.54      inference('sup-', [status(thm)], ['10', '13'])).
% 1.35/1.54  thf(commutativity_k2_tarski, axiom,
% 1.35/1.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.35/1.54  thf('15', plain,
% 1.35/1.54      (![X20 : $i, X21 : $i]:
% 1.35/1.54         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.35/1.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.35/1.54  thf(t100_xboole_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.35/1.54  thf('16', plain,
% 1.35/1.54      (![X12 : $i, X13 : $i]:
% 1.35/1.54         ((k4_xboole_0 @ X12 @ X13)
% 1.35/1.54           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.35/1.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.35/1.54  thf('17', plain,
% 1.35/1.54      (![X29 : $i, X30 : $i]:
% 1.35/1.54         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 1.35/1.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.35/1.54  thf('18', plain,
% 1.35/1.54      (![X12 : $i, X13 : $i]:
% 1.35/1.54         ((k4_xboole_0 @ X12 @ X13)
% 1.35/1.54           = (k5_xboole_0 @ X12 @ (k1_setfam_1 @ (k2_tarski @ X12 @ X13))))),
% 1.35/1.54      inference('demod', [status(thm)], ['16', '17'])).
% 1.35/1.54  thf('19', plain,
% 1.35/1.54      (![X0 : $i, X1 : $i]:
% 1.35/1.54         ((k4_xboole_0 @ X0 @ X1)
% 1.35/1.54           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.35/1.54      inference('sup+', [status(thm)], ['15', '18'])).
% 1.35/1.54  thf('20', plain,
% 1.35/1.54      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['14', '19'])).
% 1.35/1.54  thf('21', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(d5_subset_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.35/1.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.35/1.54  thf('22', plain,
% 1.35/1.54      (![X22 : $i, X23 : $i]:
% 1.35/1.54         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 1.35/1.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 1.35/1.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.35/1.54  thf('23', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup-', [status(thm)], ['21', '22'])).
% 1.35/1.54  thf('24', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['20', '23'])).
% 1.35/1.54  thf('25', plain,
% 1.35/1.54      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.35/1.54        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.35/1.54  thf('26', plain,
% 1.35/1.54      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.35/1.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['3', '25'])).
% 1.35/1.54  thf('27', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup-', [status(thm)], ['21', '22'])).
% 1.35/1.54  thf(t36_xboole_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.35/1.54  thf('28', plain,
% 1.35/1.54      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 1.35/1.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.35/1.54  thf('29', plain,
% 1.35/1.54      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.35/1.54        (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['27', '28'])).
% 1.35/1.54  thf('30', plain,
% 1.35/1.54      (![X31 : $i, X33 : $i]:
% 1.35/1.54         ((m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X33)) | ~ (r1_tarski @ X31 @ X33))),
% 1.35/1.54      inference('cnf', [status(esa)], [t3_subset])).
% 1.35/1.54  thf('31', plain,
% 1.35/1.54      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.35/1.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['29', '30'])).
% 1.35/1.54  thf(t52_pre_topc, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( l1_pre_topc @ A ) =>
% 1.35/1.54       ( ![B:$i]:
% 1.35/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.35/1.54           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.35/1.54             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.35/1.54               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.35/1.54  thf('32', plain,
% 1.35/1.54      (![X36 : $i, X37 : $i]:
% 1.35/1.54         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.35/1.54          | ~ (v4_pre_topc @ X36 @ X37)
% 1.35/1.54          | ((k2_pre_topc @ X37 @ X36) = (X36))
% 1.35/1.54          | ~ (l1_pre_topc @ X37))),
% 1.35/1.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.35/1.54  thf('33', plain,
% 1.35/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.35/1.54        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.35/1.54            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.35/1.54        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['31', '32'])).
% 1.35/1.54  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('35', plain,
% 1.35/1.54      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.35/1.54          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.35/1.54        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['33', '34'])).
% 1.35/1.54  thf('36', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['20', '23'])).
% 1.35/1.54  thf('37', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['20', '23'])).
% 1.35/1.54  thf('38', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['20', '23'])).
% 1.35/1.54  thf('39', plain,
% 1.35/1.54      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.35/1.54          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.35/1.54        | ~ (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.35/1.54  thf('40', plain,
% 1.35/1.54      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.35/1.54          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.35/1.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['26', '39'])).
% 1.35/1.54  thf('41', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(d1_tops_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( l1_pre_topc @ A ) =>
% 1.35/1.54       ( ![B:$i]:
% 1.35/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.35/1.54           ( ( k1_tops_1 @ A @ B ) =
% 1.35/1.54             ( k3_subset_1 @
% 1.35/1.54               ( u1_struct_0 @ A ) @ 
% 1.35/1.54               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.35/1.54  thf('42', plain,
% 1.35/1.54      (![X38 : $i, X39 : $i]:
% 1.35/1.54         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.35/1.54          | ((k1_tops_1 @ X39 @ X38)
% 1.35/1.54              = (k3_subset_1 @ (u1_struct_0 @ X39) @ 
% 1.35/1.54                 (k2_pre_topc @ X39 @ (k3_subset_1 @ (u1_struct_0 @ X39) @ X38))))
% 1.35/1.54          | ~ (l1_pre_topc @ X39))),
% 1.35/1.54      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.35/1.54  thf('43', plain,
% 1.35/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.35/1.54        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.35/1.54            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54               (k2_pre_topc @ sk_A @ 
% 1.35/1.54                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['41', '42'])).
% 1.35/1.54  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('45', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['20', '23'])).
% 1.35/1.54  thf('46', plain,
% 1.35/1.54      (((k1_tops_1 @ sk_A @ sk_B)
% 1.35/1.54         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.35/1.54  thf('47', plain,
% 1.35/1.54      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.35/1.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('sup+', [status(thm)], ['40', '46'])).
% 1.35/1.54  thf('48', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(involutiveness_k3_subset_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.35/1.54       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.35/1.54  thf('49', plain,
% 1.35/1.54      (![X24 : $i, X25 : $i]:
% 1.35/1.54         (((k3_subset_1 @ X25 @ (k3_subset_1 @ X25 @ X24)) = (X24))
% 1.35/1.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 1.35/1.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.35/1.54  thf('50', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.35/1.54      inference('sup-', [status(thm)], ['48', '49'])).
% 1.35/1.54  thf('51', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.35/1.54         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['20', '23'])).
% 1.35/1.54  thf('52', plain,
% 1.35/1.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.35/1.54      inference('demod', [status(thm)], ['50', '51'])).
% 1.35/1.54  thf('53', plain,
% 1.35/1.54      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.35/1.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('sup+', [status(thm)], ['47', '52'])).
% 1.35/1.54  thf('54', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(l78_tops_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( l1_pre_topc @ A ) =>
% 1.35/1.54       ( ![B:$i]:
% 1.35/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.35/1.54           ( ( k2_tops_1 @ A @ B ) =
% 1.35/1.54             ( k7_subset_1 @
% 1.35/1.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.35/1.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.35/1.54  thf('55', plain,
% 1.35/1.54      (![X42 : $i, X43 : $i]:
% 1.35/1.54         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.35/1.54          | ((k2_tops_1 @ X43 @ X42)
% 1.35/1.54              = (k7_subset_1 @ (u1_struct_0 @ X43) @ 
% 1.35/1.54                 (k2_pre_topc @ X43 @ X42) @ (k1_tops_1 @ X43 @ X42)))
% 1.35/1.54          | ~ (l1_pre_topc @ X43))),
% 1.35/1.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.35/1.54  thf('56', plain,
% 1.35/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.35/1.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['54', '55'])).
% 1.35/1.54  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('58', plain,
% 1.35/1.54      (((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.35/1.54            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.35/1.54      inference('demod', [status(thm)], ['56', '57'])).
% 1.35/1.54  thf('59', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.35/1.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('sup+', [status(thm)], ['53', '58'])).
% 1.35/1.54  thf('60', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('split', [status(esa)], ['0'])).
% 1.35/1.54  thf('61', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.35/1.54             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['59', '60'])).
% 1.35/1.54  thf('62', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.35/1.54       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('simplify', [status(thm)], ['61'])).
% 1.35/1.54  thf('63', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.35/1.54       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('split', [status(esa)], ['2'])).
% 1.35/1.54  thf(d4_xboole_0, axiom,
% 1.35/1.54    (![A:$i,B:$i,C:$i]:
% 1.35/1.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.35/1.54       ( ![D:$i]:
% 1.35/1.54         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.35/1.54  thf('64', plain,
% 1.35/1.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.35/1.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.35/1.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.35/1.54  thf('65', plain,
% 1.35/1.54      (![X29 : $i, X30 : $i]:
% 1.35/1.54         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 1.35/1.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.35/1.54  thf('66', plain,
% 1.35/1.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.35/1.54         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.35/1.54      inference('demod', [status(thm)], ['64', '65'])).
% 1.35/1.54  thf(t3_boole, axiom,
% 1.35/1.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.35/1.54  thf('67', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.35/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.35/1.54  thf(d5_xboole_0, axiom,
% 1.35/1.54    (![A:$i,B:$i,C:$i]:
% 1.35/1.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.35/1.54       ( ![D:$i]:
% 1.35/1.54         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.35/1.54  thf('68', plain,
% 1.35/1.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X10 @ X9)
% 1.35/1.54          | ~ (r2_hidden @ X10 @ X8)
% 1.35/1.54          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.35/1.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.35/1.54  thf('69', plain,
% 1.35/1.54      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X10 @ X8)
% 1.35/1.54          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.35/1.54      inference('simplify', [status(thm)], ['68'])).
% 1.35/1.54  thf('70', plain,
% 1.35/1.54      (![X0 : $i, X1 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.35/1.54      inference('sup-', [status(thm)], ['67', '69'])).
% 1.35/1.54  thf('71', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.35/1.54      inference('condensation', [status(thm)], ['70'])).
% 1.35/1.54  thf('72', plain,
% 1.35/1.54      (![X0 : $i, X1 : $i]:
% 1.35/1.54         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.35/1.54          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['66', '71'])).
% 1.35/1.54  thf('73', plain,
% 1.35/1.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.35/1.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.35/1.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.35/1.54  thf('74', plain,
% 1.35/1.54      (![X29 : $i, X30 : $i]:
% 1.35/1.54         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 1.35/1.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.35/1.54  thf('75', plain,
% 1.35/1.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.35/1.54         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.35/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.35/1.54      inference('demod', [status(thm)], ['73', '74'])).
% 1.35/1.54  thf('76', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.35/1.54      inference('condensation', [status(thm)], ['70'])).
% 1.35/1.54  thf('77', plain,
% 1.35/1.54      (![X0 : $i, X1 : $i]:
% 1.35/1.54         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.35/1.54          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['75', '76'])).
% 1.35/1.54  thf('78', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(dt_k2_pre_topc, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( ( l1_pre_topc @ A ) & 
% 1.35/1.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.35/1.54       ( m1_subset_1 @
% 1.35/1.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.35/1.54  thf('79', plain,
% 1.35/1.54      (![X34 : $i, X35 : $i]:
% 1.35/1.54         (~ (l1_pre_topc @ X34)
% 1.35/1.54          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.35/1.54          | (m1_subset_1 @ (k2_pre_topc @ X34 @ X35) @ 
% 1.35/1.54             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 1.35/1.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.35/1.54  thf('80', plain,
% 1.35/1.54      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.35/1.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.35/1.54        | ~ (l1_pre_topc @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['78', '79'])).
% 1.35/1.54  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('82', plain,
% 1.35/1.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.35/1.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('demod', [status(thm)], ['80', '81'])).
% 1.35/1.54  thf(redefinition_k7_subset_1, axiom,
% 1.35/1.54    (![A:$i,B:$i,C:$i]:
% 1.35/1.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.35/1.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.35/1.54  thf('83', plain,
% 1.35/1.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.54         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.35/1.54          | ((k7_subset_1 @ X27 @ X26 @ X28) = (k4_xboole_0 @ X26 @ X28)))),
% 1.35/1.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.35/1.54  thf('84', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.35/1.54           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.35/1.54      inference('sup-', [status(thm)], ['82', '83'])).
% 1.35/1.54  thf('85', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('split', [status(esa)], ['2'])).
% 1.35/1.54  thf('86', plain,
% 1.35/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('sup+', [status(thm)], ['84', '85'])).
% 1.35/1.54  thf('87', plain,
% 1.35/1.54      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X10 @ X8)
% 1.35/1.54          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.35/1.54      inference('simplify', [status(thm)], ['68'])).
% 1.35/1.54  thf('88', plain,
% 1.35/1.54      ((![X0 : $i]:
% 1.35/1.54          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.35/1.54           | ~ (r2_hidden @ X0 @ sk_B)))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['86', '87'])).
% 1.35/1.54  thf('89', plain,
% 1.35/1.54      ((![X0 : $i]:
% 1.35/1.54          (((k1_xboole_0)
% 1.35/1.54             = (k1_setfam_1 @ (k2_tarski @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.35/1.54           | ~ (r2_hidden @ 
% 1.35/1.54                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['77', '88'])).
% 1.35/1.54  thf('90', plain,
% 1.35/1.54      (((((k1_xboole_0)
% 1.35/1.54           = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.35/1.54         | ((k1_xboole_0)
% 1.35/1.54             = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['72', '89'])).
% 1.35/1.54  thf('91', plain,
% 1.35/1.54      ((((k1_xboole_0)
% 1.35/1.54          = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('simplify', [status(thm)], ['90'])).
% 1.35/1.54  thf('92', plain,
% 1.35/1.54      (![X12 : $i, X13 : $i]:
% 1.35/1.54         ((k4_xboole_0 @ X12 @ X13)
% 1.35/1.54           = (k5_xboole_0 @ X12 @ (k1_setfam_1 @ (k2_tarski @ X12 @ X13))))),
% 1.35/1.54      inference('demod', [status(thm)], ['16', '17'])).
% 1.35/1.54  thf('93', plain,
% 1.35/1.54      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.35/1.54          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('sup+', [status(thm)], ['91', '92'])).
% 1.35/1.54  thf(t2_boole, axiom,
% 1.35/1.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.35/1.54  thf('94', plain,
% 1.35/1.54      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.35/1.54      inference('cnf', [status(esa)], [t2_boole])).
% 1.35/1.54  thf('95', plain,
% 1.35/1.54      (![X29 : $i, X30 : $i]:
% 1.35/1.54         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 1.35/1.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.35/1.54  thf('96', plain,
% 1.35/1.54      (![X16 : $i]:
% 1.35/1.54         ((k1_setfam_1 @ (k2_tarski @ X16 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.35/1.54      inference('demod', [status(thm)], ['94', '95'])).
% 1.35/1.54  thf('97', plain,
% 1.35/1.54      (![X12 : $i, X13 : $i]:
% 1.35/1.54         ((k4_xboole_0 @ X12 @ X13)
% 1.35/1.54           = (k5_xboole_0 @ X12 @ (k1_setfam_1 @ (k2_tarski @ X12 @ X13))))),
% 1.35/1.54      inference('demod', [status(thm)], ['16', '17'])).
% 1.35/1.54  thf('98', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.35/1.54      inference('sup+', [status(thm)], ['96', '97'])).
% 1.35/1.54  thf('99', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.35/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.35/1.54  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.35/1.54      inference('sup+', [status(thm)], ['98', '99'])).
% 1.35/1.54  thf('101', plain,
% 1.35/1.54      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['93', '100'])).
% 1.35/1.54  thf('102', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(t74_tops_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( l1_pre_topc @ A ) =>
% 1.35/1.54       ( ![B:$i]:
% 1.35/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.35/1.54           ( ( k1_tops_1 @ A @ B ) =
% 1.35/1.54             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.35/1.54  thf('103', plain,
% 1.35/1.54      (![X46 : $i, X47 : $i]:
% 1.35/1.54         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.35/1.54          | ((k1_tops_1 @ X47 @ X46)
% 1.35/1.54              = (k7_subset_1 @ (u1_struct_0 @ X47) @ X46 @ 
% 1.35/1.54                 (k2_tops_1 @ X47 @ X46)))
% 1.35/1.54          | ~ (l1_pre_topc @ X47))),
% 1.35/1.54      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.35/1.54  thf('104', plain,
% 1.35/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.35/1.54        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.35/1.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.35/1.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['102', '103'])).
% 1.35/1.54  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('106', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('107', plain,
% 1.35/1.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.54         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.35/1.54          | ((k7_subset_1 @ X27 @ X26 @ X28) = (k4_xboole_0 @ X26 @ X28)))),
% 1.35/1.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.35/1.54  thf('108', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.35/1.54           = (k4_xboole_0 @ sk_B @ X0))),
% 1.35/1.54      inference('sup-', [status(thm)], ['106', '107'])).
% 1.35/1.54  thf('109', plain,
% 1.35/1.54      (((k1_tops_1 @ sk_A @ sk_B)
% 1.35/1.54         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.35/1.54      inference('demod', [status(thm)], ['104', '105', '108'])).
% 1.35/1.54  thf('110', plain,
% 1.35/1.54      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('sup+', [status(thm)], ['101', '109'])).
% 1.35/1.54  thf('111', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(fc9_tops_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.35/1.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.35/1.54       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.35/1.54  thf('112', plain,
% 1.35/1.54      (![X40 : $i, X41 : $i]:
% 1.35/1.54         (~ (l1_pre_topc @ X40)
% 1.35/1.54          | ~ (v2_pre_topc @ X40)
% 1.35/1.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.35/1.54          | (v3_pre_topc @ (k1_tops_1 @ X40 @ X41) @ X40))),
% 1.35/1.54      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.35/1.54  thf('113', plain,
% 1.35/1.54      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.35/1.54        | ~ (v2_pre_topc @ sk_A)
% 1.35/1.54        | ~ (l1_pre_topc @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['111', '112'])).
% 1.35/1.54  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('116', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.35/1.54      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.35/1.54  thf('117', plain,
% 1.35/1.54      (((v3_pre_topc @ sk_B @ sk_A))
% 1.35/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.35/1.54      inference('sup+', [status(thm)], ['110', '116'])).
% 1.35/1.54  thf('118', plain,
% 1.35/1.54      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.35/1.54      inference('split', [status(esa)], ['0'])).
% 1.35/1.54  thf('119', plain,
% 1.35/1.54      (~
% 1.35/1.54       (((k2_tops_1 @ sk_A @ sk_B)
% 1.35/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.35/1.54       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['117', '118'])).
% 1.35/1.54  thf('120', plain, ($false),
% 1.35/1.54      inference('sat_resolution*', [status(thm)], ['1', '62', '63', '119'])).
% 1.35/1.54  
% 1.35/1.54  % SZS output end Refutation
% 1.35/1.54  
% 1.35/1.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
