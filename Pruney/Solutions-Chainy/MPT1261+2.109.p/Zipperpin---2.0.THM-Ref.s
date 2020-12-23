%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rtyLIIypgp

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:54 EST 2020

% Result     : Theorem 5.14s
% Output     : Refutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 358 expanded)
%              Number of leaves         :   35 ( 114 expanded)
%              Depth                    :   17
%              Number of atoms          : 1273 (4685 expanded)
%              Number of equality atoms :   85 ( 236 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k2_pre_topc @ X33 @ X32 ) @ ( k1_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
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
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('50',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('52',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('56',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('59',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63','78'])).

thf('80',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('81',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('83',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('84',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rtyLIIypgp
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.14/5.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.14/5.37  % Solved by: fo/fo7.sh
% 5.14/5.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.14/5.37  % done 1492 iterations in 4.918s
% 5.14/5.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.14/5.37  % SZS output start Refutation
% 5.14/5.37  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.14/5.37  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.14/5.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.14/5.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.14/5.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.14/5.37  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.14/5.37  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.14/5.37  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.14/5.37  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.14/5.37  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.14/5.37  thf(sk_A_type, type, sk_A: $i).
% 5.14/5.37  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.14/5.37  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.14/5.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.14/5.37  thf(sk_B_type, type, sk_B: $i).
% 5.14/5.37  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.14/5.37  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.14/5.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.14/5.37  thf(t77_tops_1, conjecture,
% 5.14/5.37    (![A:$i]:
% 5.14/5.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.14/5.37       ( ![B:$i]:
% 5.14/5.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.14/5.37           ( ( v4_pre_topc @ B @ A ) <=>
% 5.14/5.37             ( ( k2_tops_1 @ A @ B ) =
% 5.14/5.37               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 5.14/5.37  thf(zf_stmt_0, negated_conjecture,
% 5.14/5.37    (~( ![A:$i]:
% 5.14/5.37        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.14/5.37          ( ![B:$i]:
% 5.14/5.37            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.14/5.37              ( ( v4_pre_topc @ B @ A ) <=>
% 5.14/5.37                ( ( k2_tops_1 @ A @ B ) =
% 5.14/5.37                  ( k7_subset_1 @
% 5.14/5.37                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 5.14/5.37    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 5.14/5.37  thf('0', plain,
% 5.14/5.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.37              (k1_tops_1 @ sk_A @ sk_B)))
% 5.14/5.37        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.37  thf('1', plain,
% 5.14/5.37      (~
% 5.14/5.37       (((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.37             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.14/5.37       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.37      inference('split', [status(esa)], ['0'])).
% 5.14/5.37  thf('2', plain,
% 5.14/5.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.37             (k1_tops_1 @ sk_A @ sk_B)))
% 5.14/5.37        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.37  thf('3', plain,
% 5.14/5.37      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.14/5.37      inference('split', [status(esa)], ['2'])).
% 5.14/5.37  thf('4', plain,
% 5.14/5.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.37  thf(t52_pre_topc, axiom,
% 5.14/5.37    (![A:$i]:
% 5.14/5.37     ( ( l1_pre_topc @ A ) =>
% 5.14/5.37       ( ![B:$i]:
% 5.14/5.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.14/5.37           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 5.14/5.37             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 5.14/5.37               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 5.14/5.37  thf('5', plain,
% 5.14/5.37      (![X26 : $i, X27 : $i]:
% 5.14/5.37         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.14/5.37          | ~ (v4_pre_topc @ X26 @ X27)
% 5.14/5.37          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 5.14/5.37          | ~ (l1_pre_topc @ X27))),
% 5.14/5.37      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.14/5.37  thf('6', plain,
% 5.14/5.37      ((~ (l1_pre_topc @ sk_A)
% 5.14/5.37        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 5.14/5.37        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.37      inference('sup-', [status(thm)], ['4', '5'])).
% 5.14/5.37  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.37  thf('8', plain,
% 5.14/5.37      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.37      inference('demod', [status(thm)], ['6', '7'])).
% 5.14/5.37  thf('9', plain,
% 5.14/5.37      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 5.14/5.37         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['3', '8'])).
% 5.14/5.37  thf('10', plain,
% 5.14/5.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.37  thf(l78_tops_1, axiom,
% 5.14/5.37    (![A:$i]:
% 5.14/5.37     ( ( l1_pre_topc @ A ) =>
% 5.14/5.37       ( ![B:$i]:
% 5.14/5.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.14/5.37           ( ( k2_tops_1 @ A @ B ) =
% 5.14/5.37             ( k7_subset_1 @
% 5.14/5.37               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.14/5.37               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.14/5.37  thf('11', plain,
% 5.14/5.37      (![X32 : $i, X33 : $i]:
% 5.14/5.37         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 5.14/5.37          | ((k2_tops_1 @ X33 @ X32)
% 5.14/5.37              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 5.14/5.37                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 5.14/5.37          | ~ (l1_pre_topc @ X33))),
% 5.14/5.37      inference('cnf', [status(esa)], [l78_tops_1])).
% 5.14/5.37  thf('12', plain,
% 5.14/5.37      ((~ (l1_pre_topc @ sk_A)
% 5.14/5.37        | ((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.14/5.37               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.14/5.37      inference('sup-', [status(thm)], ['10', '11'])).
% 5.14/5.37  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.37  thf('14', plain,
% 5.14/5.37      (((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.14/5.37            (k1_tops_1 @ sk_A @ sk_B)))),
% 5.14/5.37      inference('demod', [status(thm)], ['12', '13'])).
% 5.14/5.37  thf('15', plain,
% 5.14/5.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.37             (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.37         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['9', '14'])).
% 5.14/5.37  thf('16', plain,
% 5.14/5.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.37  thf(redefinition_k7_subset_1, axiom,
% 5.14/5.37    (![A:$i,B:$i,C:$i]:
% 5.14/5.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.14/5.37       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 5.14/5.37  thf('17', plain,
% 5.14/5.37      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.14/5.37         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 5.14/5.37          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 5.14/5.37      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 5.14/5.37  thf('18', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.14/5.37           = (k4_xboole_0 @ sk_B @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['16', '17'])).
% 5.14/5.37  thf('19', plain,
% 5.14/5.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.37         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.14/5.37      inference('demod', [status(thm)], ['15', '18'])).
% 5.14/5.37  thf('20', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.14/5.37           = (k4_xboole_0 @ sk_B @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['16', '17'])).
% 5.14/5.37  thf('21', plain,
% 5.14/5.37      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.37          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.37              (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.38         <= (~
% 5.14/5.38             (((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('split', [status(esa)], ['0'])).
% 5.14/5.38  thf('22', plain,
% 5.14/5.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.38         <= (~
% 5.14/5.38             (((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup-', [status(thm)], ['20', '21'])).
% 5.14/5.38  thf('23', plain,
% 5.14/5.38      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 5.14/5.38         <= (~
% 5.14/5.38             (((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 5.14/5.38             ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.14/5.38      inference('sup-', [status(thm)], ['19', '22'])).
% 5.14/5.38  thf('24', plain,
% 5.14/5.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.14/5.38       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.38      inference('simplify', [status(thm)], ['23'])).
% 5.14/5.38  thf('25', plain,
% 5.14/5.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.14/5.38       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.38      inference('split', [status(esa)], ['2'])).
% 5.14/5.38  thf('26', plain,
% 5.14/5.38      (![X0 : $i]:
% 5.14/5.38         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.14/5.38           = (k4_xboole_0 @ sk_B @ X0))),
% 5.14/5.38      inference('sup-', [status(thm)], ['16', '17'])).
% 5.14/5.38  thf('27', plain,
% 5.14/5.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38             (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('split', [status(esa)], ['2'])).
% 5.14/5.38  thf('28', plain,
% 5.14/5.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['26', '27'])).
% 5.14/5.38  thf('29', plain,
% 5.14/5.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf(t44_tops_1, axiom,
% 5.14/5.38    (![A:$i]:
% 5.14/5.38     ( ( l1_pre_topc @ A ) =>
% 5.14/5.38       ( ![B:$i]:
% 5.14/5.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.14/5.38           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 5.14/5.38  thf('30', plain,
% 5.14/5.38      (![X34 : $i, X35 : $i]:
% 5.14/5.38         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.14/5.38          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ X34)
% 5.14/5.38          | ~ (l1_pre_topc @ X35))),
% 5.14/5.38      inference('cnf', [status(esa)], [t44_tops_1])).
% 5.14/5.38  thf('31', plain,
% 5.14/5.38      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 5.14/5.38      inference('sup-', [status(thm)], ['29', '30'])).
% 5.14/5.38  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf('33', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.14/5.38      inference('demod', [status(thm)], ['31', '32'])).
% 5.14/5.38  thf(t3_subset, axiom,
% 5.14/5.38    (![A:$i,B:$i]:
% 5.14/5.38     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.14/5.38  thf('34', plain,
% 5.14/5.38      (![X23 : $i, X25 : $i]:
% 5.14/5.38         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 5.14/5.38      inference('cnf', [status(esa)], [t3_subset])).
% 5.14/5.38  thf('35', plain,
% 5.14/5.38      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.14/5.38      inference('sup-', [status(thm)], ['33', '34'])).
% 5.14/5.38  thf(dt_k3_subset_1, axiom,
% 5.14/5.38    (![A:$i,B:$i]:
% 5.14/5.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.14/5.38       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.14/5.38  thf('36', plain,
% 5.14/5.38      (![X13 : $i, X14 : $i]:
% 5.14/5.38         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 5.14/5.38          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 5.14/5.38      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 5.14/5.38  thf('37', plain,
% 5.14/5.38      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.14/5.38        (k1_zfmisc_1 @ sk_B))),
% 5.14/5.38      inference('sup-', [status(thm)], ['35', '36'])).
% 5.14/5.38  thf('38', plain,
% 5.14/5.38      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.14/5.38      inference('sup-', [status(thm)], ['33', '34'])).
% 5.14/5.38  thf(d5_subset_1, axiom,
% 5.14/5.38    (![A:$i,B:$i]:
% 5.14/5.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.14/5.38       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.14/5.38  thf('39', plain,
% 5.14/5.38      (![X11 : $i, X12 : $i]:
% 5.14/5.38         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 5.14/5.38          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 5.14/5.38      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.14/5.38  thf('40', plain,
% 5.14/5.38      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.14/5.38         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.14/5.38      inference('sup-', [status(thm)], ['38', '39'])).
% 5.14/5.38  thf('41', plain,
% 5.14/5.38      ((m1_subset_1 @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.14/5.38        (k1_zfmisc_1 @ sk_B))),
% 5.14/5.38      inference('demod', [status(thm)], ['37', '40'])).
% 5.14/5.38  thf('42', plain,
% 5.14/5.38      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['28', '41'])).
% 5.14/5.38  thf('43', plain,
% 5.14/5.38      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.14/5.38      inference('sup-', [status(thm)], ['33', '34'])).
% 5.14/5.38  thf(redefinition_k4_subset_1, axiom,
% 5.14/5.38    (![A:$i,B:$i,C:$i]:
% 5.14/5.38     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.14/5.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.14/5.38       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.14/5.38  thf('44', plain,
% 5.14/5.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.14/5.38         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 5.14/5.38          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 5.14/5.38          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 5.14/5.38      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.14/5.38  thf('45', plain,
% 5.14/5.38      (![X0 : $i]:
% 5.14/5.38         (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 5.14/5.38            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 5.14/5.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 5.14/5.38      inference('sup-', [status(thm)], ['43', '44'])).
% 5.14/5.38  thf('46', plain,
% 5.14/5.38      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38          (k2_tops_1 @ sk_A @ sk_B))
% 5.14/5.38          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38             (k2_tops_1 @ sk_A @ sk_B))))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup-', [status(thm)], ['42', '45'])).
% 5.14/5.38  thf(commutativity_k2_xboole_0, axiom,
% 5.14/5.38    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.14/5.38  thf('47', plain,
% 5.14/5.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.14/5.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.14/5.38  thf('48', plain,
% 5.14/5.38      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38          (k2_tops_1 @ sk_A @ sk_B))
% 5.14/5.38          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38             (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('demod', [status(thm)], ['46', '47'])).
% 5.14/5.38  thf('49', plain,
% 5.14/5.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['26', '27'])).
% 5.14/5.38  thf('50', plain,
% 5.14/5.38      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.14/5.38      inference('sup-', [status(thm)], ['33', '34'])).
% 5.14/5.38  thf(t25_subset_1, axiom,
% 5.14/5.38    (![A:$i,B:$i]:
% 5.14/5.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.14/5.38       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 5.14/5.38         ( k2_subset_1 @ A ) ) ))).
% 5.14/5.38  thf('51', plain,
% 5.14/5.38      (![X21 : $i, X22 : $i]:
% 5.14/5.38         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 5.14/5.38            = (k2_subset_1 @ X21))
% 5.14/5.38          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 5.14/5.38      inference('cnf', [status(esa)], [t25_subset_1])).
% 5.14/5.38  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.14/5.38  thf('52', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 5.14/5.38      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.14/5.38  thf('53', plain,
% 5.14/5.38      (![X21 : $i, X22 : $i]:
% 5.14/5.38         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 5.14/5.38          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 5.14/5.38      inference('demod', [status(thm)], ['51', '52'])).
% 5.14/5.38  thf('54', plain,
% 5.14/5.38      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38         (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 5.14/5.38      inference('sup-', [status(thm)], ['50', '53'])).
% 5.14/5.38  thf('55', plain,
% 5.14/5.38      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.14/5.38         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.14/5.38      inference('sup-', [status(thm)], ['38', '39'])).
% 5.14/5.38  thf('56', plain,
% 5.14/5.38      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38         (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 5.14/5.38      inference('demod', [status(thm)], ['54', '55'])).
% 5.14/5.38  thf('57', plain,
% 5.14/5.38      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['49', '56'])).
% 5.14/5.38  thf('58', plain,
% 5.14/5.38      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 5.14/5.38          = (sk_B)))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['48', '57'])).
% 5.14/5.38  thf(idempotence_k2_xboole_0, axiom,
% 5.14/5.38    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 5.14/5.38  thf('59', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 5.14/5.38      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 5.14/5.38  thf(t4_xboole_1, axiom,
% 5.14/5.38    (![A:$i,B:$i,C:$i]:
% 5.14/5.38     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 5.14/5.38       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.14/5.38  thf('60', plain,
% 5.14/5.38      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.14/5.38         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 5.14/5.38           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 5.14/5.38      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.14/5.38  thf('61', plain,
% 5.14/5.38      (![X0 : $i, X1 : $i]:
% 5.14/5.38         ((k2_xboole_0 @ X0 @ X1)
% 5.14/5.38           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 5.14/5.38      inference('sup+', [status(thm)], ['59', '60'])).
% 5.14/5.38  thf('62', plain,
% 5.14/5.38      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 5.14/5.38          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['58', '61'])).
% 5.14/5.38  thf('63', plain,
% 5.14/5.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.14/5.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.14/5.38  thf('64', plain,
% 5.14/5.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf(dt_k2_tops_1, axiom,
% 5.14/5.38    (![A:$i,B:$i]:
% 5.14/5.38     ( ( ( l1_pre_topc @ A ) & 
% 5.14/5.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.14/5.38       ( m1_subset_1 @
% 5.14/5.38         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.14/5.38  thf('65', plain,
% 5.14/5.38      (![X28 : $i, X29 : $i]:
% 5.14/5.38         (~ (l1_pre_topc @ X28)
% 5.14/5.38          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 5.14/5.38          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 5.14/5.38             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 5.14/5.38      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 5.14/5.38  thf('66', plain,
% 5.14/5.38      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.14/5.38        | ~ (l1_pre_topc @ sk_A))),
% 5.14/5.38      inference('sup-', [status(thm)], ['64', '65'])).
% 5.14/5.38  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf('68', plain,
% 5.14/5.38      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.14/5.38        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.38      inference('demod', [status(thm)], ['66', '67'])).
% 5.14/5.38  thf('69', plain,
% 5.14/5.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf('70', plain,
% 5.14/5.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.14/5.38         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 5.14/5.38          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 5.14/5.38          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 5.14/5.38      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.14/5.38  thf('71', plain,
% 5.14/5.38      (![X0 : $i]:
% 5.14/5.38         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.14/5.38            = (k2_xboole_0 @ sk_B @ X0))
% 5.14/5.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.14/5.38      inference('sup-', [status(thm)], ['69', '70'])).
% 5.14/5.38  thf('72', plain,
% 5.14/5.38      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 5.14/5.38         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.14/5.38      inference('sup-', [status(thm)], ['68', '71'])).
% 5.14/5.38  thf('73', plain,
% 5.14/5.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf(t65_tops_1, axiom,
% 5.14/5.38    (![A:$i]:
% 5.14/5.38     ( ( l1_pre_topc @ A ) =>
% 5.14/5.38       ( ![B:$i]:
% 5.14/5.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.14/5.38           ( ( k2_pre_topc @ A @ B ) =
% 5.14/5.38             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.14/5.38  thf('74', plain,
% 5.14/5.38      (![X36 : $i, X37 : $i]:
% 5.14/5.38         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 5.14/5.38          | ((k2_pre_topc @ X37 @ X36)
% 5.14/5.38              = (k4_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 5.14/5.38                 (k2_tops_1 @ X37 @ X36)))
% 5.14/5.38          | ~ (l1_pre_topc @ X37))),
% 5.14/5.38      inference('cnf', [status(esa)], [t65_tops_1])).
% 5.14/5.38  thf('75', plain,
% 5.14/5.38      ((~ (l1_pre_topc @ sk_A)
% 5.14/5.38        | ((k2_pre_topc @ sk_A @ sk_B)
% 5.14/5.38            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38               (k2_tops_1 @ sk_A @ sk_B))))),
% 5.14/5.38      inference('sup-', [status(thm)], ['73', '74'])).
% 5.14/5.38  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf('77', plain,
% 5.14/5.38      (((k2_pre_topc @ sk_A @ sk_B)
% 5.14/5.38         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38            (k2_tops_1 @ sk_A @ sk_B)))),
% 5.14/5.38      inference('demod', [status(thm)], ['75', '76'])).
% 5.14/5.38  thf('78', plain,
% 5.14/5.38      (((k2_pre_topc @ sk_A @ sk_B)
% 5.14/5.38         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.14/5.38      inference('sup+', [status(thm)], ['72', '77'])).
% 5.14/5.38  thf('79', plain,
% 5.14/5.38      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 5.14/5.38          = (k2_pre_topc @ sk_A @ sk_B)))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('demod', [status(thm)], ['62', '63', '78'])).
% 5.14/5.38  thf('80', plain,
% 5.14/5.38      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 5.14/5.38          = (sk_B)))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['48', '57'])).
% 5.14/5.38  thf('81', plain,
% 5.14/5.38      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['79', '80'])).
% 5.14/5.38  thf('82', plain,
% 5.14/5.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf(fc1_tops_1, axiom,
% 5.14/5.38    (![A:$i,B:$i]:
% 5.14/5.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 5.14/5.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.14/5.38       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 5.14/5.38  thf('83', plain,
% 5.14/5.38      (![X30 : $i, X31 : $i]:
% 5.14/5.38         (~ (l1_pre_topc @ X30)
% 5.14/5.38          | ~ (v2_pre_topc @ X30)
% 5.14/5.38          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 5.14/5.38          | (v4_pre_topc @ (k2_pre_topc @ X30 @ X31) @ X30))),
% 5.14/5.38      inference('cnf', [status(esa)], [fc1_tops_1])).
% 5.14/5.38  thf('84', plain,
% 5.14/5.38      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 5.14/5.38        | ~ (v2_pre_topc @ sk_A)
% 5.14/5.38        | ~ (l1_pre_topc @ sk_A))),
% 5.14/5.38      inference('sup-', [status(thm)], ['82', '83'])).
% 5.14/5.38  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 5.14/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.38  thf('87', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 5.14/5.38      inference('demod', [status(thm)], ['84', '85', '86'])).
% 5.14/5.38  thf('88', plain,
% 5.14/5.38      (((v4_pre_topc @ sk_B @ sk_A))
% 5.14/5.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.14/5.38      inference('sup+', [status(thm)], ['81', '87'])).
% 5.14/5.38  thf('89', plain,
% 5.14/5.38      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.14/5.38      inference('split', [status(esa)], ['0'])).
% 5.14/5.38  thf('90', plain,
% 5.14/5.38      (~
% 5.14/5.38       (((k2_tops_1 @ sk_A @ sk_B)
% 5.14/5.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.14/5.38             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.14/5.38       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.14/5.38      inference('sup-', [status(thm)], ['88', '89'])).
% 5.14/5.38  thf('91', plain, ($false),
% 5.14/5.38      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '90'])).
% 5.14/5.38  
% 5.14/5.38  % SZS output end Refutation
% 5.14/5.38  
% 5.14/5.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
