%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j6Op1HWWJu

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 155 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  917 (1965 expanded)
%              Number of equality atoms :   66 ( 115 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_tops_1 @ X29 @ X28 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k2_pre_topc @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_pre_topc @ X31 @ X30 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 @ ( k2_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('56',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('61',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('62',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','65'])).

thf('67',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j6Op1HWWJu
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 152 iterations in 0.083s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(t77_tops_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.54             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.54               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.54                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.54                  ( k7_subset_1 @
% 0.20/0.54                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54              (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54             (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.54        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t52_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.54             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.54               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.54          | ~ (v4_pre_topc @ X22 @ X23)
% 0.20/0.54          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.20/0.54          | ~ (l1_pre_topc @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(l78_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.54             ( k7_subset_1 @
% 0.20/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.54          | ((k2_tops_1 @ X29 @ X28)
% 0.20/0.54              = (k7_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.20/0.54                 (k2_pre_topc @ X29 @ X28) @ (k1_tops_1 @ X29 @ X28)))
% 0.20/0.54          | ~ (l1_pre_topc @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.54            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.20/0.54          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54              (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.20/0.54             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.54       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t65_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.54             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X30 : $i, X31 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.54          | ((k2_pre_topc @ X31 @ X30)
% 0.20/0.54              = (k4_subset_1 @ (u1_struct_0 @ X31) @ X30 @ 
% 0.20/0.54                 (k2_tops_1 @ X31 @ X30)))
% 0.20/0.54          | ~ (l1_pre_topc @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.54            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_k2_tops_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54       ( m1_subset_1 @
% 0.20/0.54         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X24)
% 0.20/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.54          | (m1_subset_1 @ (k2_tops_1 @ X24 @ X25) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.20/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.20/0.54          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.54            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf(t36_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf(l32_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.20/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['42', '45'])).
% 0.20/0.54  thf(t98_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X14 @ X15)
% 0.20/0.54           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.54          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.20/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.54  thf('50', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i]:
% 0.20/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['49', '52'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X14 @ X15)
% 0.20/0.54           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf(t1_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('56', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.54  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.20/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('demod', [status(thm)], ['48', '57'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['39', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(fc1_tops_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X26)
% 0.20/0.54          | ~ (v2_pre_topc @ X26)
% 0.20/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.54          | (v4_pre_topc @ (k2_pre_topc @ X26 @ X27) @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('65', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['59', '65'])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.54       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain, ($false),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '68'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
