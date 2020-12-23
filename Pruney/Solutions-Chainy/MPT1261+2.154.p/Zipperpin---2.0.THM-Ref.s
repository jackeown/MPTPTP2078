%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nf88tIOu0D

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:01 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 198 expanded)
%              Number of leaves         :   31 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          : 1103 (2559 expanded)
%              Number of equality atoms :   74 ( 147 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(t28_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_subset_1 @ X17 @ X18 @ ( k2_subset_1 @ X17 ) )
        = ( k2_subset_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t28_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_subset_1 @ X17 @ X18 @ X17 )
        = X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k4_subset_1 @ X7 @ X6 @ X8 )
        = ( k4_subset_1 @ X7 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k4_subset_1 @ X0 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('61',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','65'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','68'])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('72',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('73',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','76'])).

thf('78',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nf88tIOu0D
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:06:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 171 iterations in 0.090s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.35/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.54  thf(t77_tops_1, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( v4_pre_topc @ B @ A ) <=>
% 0.35/0.54             ( ( k2_tops_1 @ A @ B ) =
% 0.35/0.54               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54              ( ( v4_pre_topc @ B @ A ) <=>
% 0.35/0.54                ( ( k2_tops_1 @ A @ B ) =
% 0.35/0.54                  ( k7_subset_1 @
% 0.35/0.54                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54              (k1_tops_1 @ sk_A @ sk_B)))
% 0.35/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (~
% 0.35/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.35/0.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B)))
% 0.35/0.54        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['2'])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t52_pre_topc, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.35/0.54             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.35/0.54               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X22 : $i, X23 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.54          | ~ (v4_pre_topc @ X22 @ X23)
% 0.35/0.54          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.35/0.54          | ~ (l1_pre_topc @ X23))),
% 0.35/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.35/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.54  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.35/0.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['3', '8'])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(l78_tops_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.35/0.54             ( k7_subset_1 @
% 0.35/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.35/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X28 : $i, X29 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.35/0.54          | ((k2_tops_1 @ X29 @ X28)
% 0.35/0.54              = (k7_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.35/0.54                 (k2_pre_topc @ X29 @ X28) @ (k1_tops_1 @ X29 @ X28)))
% 0.35/0.54          | ~ (l1_pre_topc @ X29))),
% 0.35/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.35/0.54            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['9', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.35/0.54          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54              (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= (~
% 0.35/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= (~
% 0.35/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.35/0.54         <= (~
% 0.35/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.35/0.54             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.35/0.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.35/0.54       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('split', [status(esa)], ['2'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t65_tops_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( k2_pre_topc @ A @ B ) =
% 0.35/0.54             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X30 : $i, X31 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.35/0.54          | ((k2_pre_topc @ X31 @ X30)
% 0.35/0.54              = (k4_subset_1 @ (u1_struct_0 @ X31) @ X30 @ 
% 0.35/0.54                 (k2_tops_1 @ X31 @ X30)))
% 0.35/0.54          | ~ (l1_pre_topc @ X31))),
% 0.35/0.54      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.35/0.54            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(dt_k2_tops_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54       ( m1_subset_1 @
% 0.35/0.54         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (![X24 : $i, X25 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X24)
% 0.35/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.35/0.54          | (m1_subset_1 @ (k2_tops_1 @ X24 @ X25) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.54  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.35/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.35/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.35/0.54          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54            = (k2_xboole_0 @ sk_B @ X0))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.35/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['34', '37'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (((k2_pre_topc @ sk_A @ sk_B)
% 0.35/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['28', '29', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('split', [status(esa)], ['2'])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.54  thf(t36_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.35/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.35/0.54  thf(t3_subset, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (![X19 : $i, X21 : $i]:
% 0.35/0.54         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.35/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['42', '45'])).
% 0.35/0.54  thf(t28_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (![X17 : $i, X18 : $i]:
% 0.35/0.54         (((k4_subset_1 @ X17 @ X18 @ (k2_subset_1 @ X17))
% 0.35/0.54            = (k2_subset_1 @ X17))
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t28_subset_1])).
% 0.35/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.54  thf('48', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.54  thf('49', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      (![X17 : $i, X18 : $i]:
% 0.35/0.54         (((k4_subset_1 @ X17 @ X18 @ X17) = (X17))
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.35/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['46', '50'])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf(dt_k2_subset_1, axiom,
% 0.35/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.35/0.54  thf('55', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.54  thf('56', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.35/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.35/0.54  thf(commutativity_k4_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.35/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 0.35/0.54          | ((k4_subset_1 @ X7 @ X6 @ X8) = (k4_subset_1 @ X7 @ X8 @ X6)))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k4_subset_1 @ X0 @ X0 @ X1) = (k4_subset_1 @ X0 @ X1 @ X0))
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k4_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.54           = (k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['53', '58'])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf('61', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.35/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.35/0.54  thf('62', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.35/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.35/0.54          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.35/0.54  thf('63', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k4_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.54           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['60', '63'])).
% 0.35/0.54  thf('65', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.54           = (k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['59', '64'])).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      ((((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.35/0.54          = (k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['52', '65'])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.54  thf('68', plain,
% 0.35/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.35/0.54          = (k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.35/0.54  thf('69', plain,
% 0.35/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['51', '68'])).
% 0.35/0.54  thf('70', plain,
% 0.35/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['39', '69'])).
% 0.35/0.54  thf('71', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(fc1_tops_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      (![X26 : $i, X27 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X26)
% 0.35/0.54          | ~ (v2_pre_topc @ X26)
% 0.35/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.35/0.54          | (v4_pre_topc @ (k2_pre_topc @ X26 @ X27) @ X26))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.35/0.54  thf('73', plain,
% 0.35/0.54      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.35/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.35/0.54  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('76', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.35/0.54  thf('77', plain,
% 0.35/0.54      (((v4_pre_topc @ sk_B @ sk_A))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['70', '76'])).
% 0.35/0.54  thf('78', plain,
% 0.35/0.54      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('79', plain,
% 0.35/0.54      (~
% 0.35/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.35/0.54       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.35/0.54  thf('80', plain, ($false),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '79'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
