%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dDZ4S2rZ27

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:59 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 328 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          : 1538 (3708 expanded)
%              Number of equality atoms :  125 ( 254 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ X33 ) @ ( k1_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['36','47'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('69',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('71',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','91'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','92'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('94',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('95',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('97',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('99',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('100',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('104',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('108',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['97','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('115',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X31 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('116',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
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
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dDZ4S2rZ27
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.49/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.69  % Solved by: fo/fo7.sh
% 0.49/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.69  % done 770 iterations in 0.221s
% 0.49/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.69  % SZS output start Refutation
% 0.49/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.49/0.69  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.49/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.49/0.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.49/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.69  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.49/0.69  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.49/0.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.49/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(t77_tops_1, conjecture,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( v4_pre_topc @ B @ A ) <=>
% 0.49/0.69             ( ( k2_tops_1 @ A @ B ) =
% 0.49/0.69               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.69    (~( ![A:$i]:
% 0.49/0.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.69          ( ![B:$i]:
% 0.49/0.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69              ( ( v4_pre_topc @ B @ A ) <=>
% 0.49/0.69                ( ( k2_tops_1 @ A @ B ) =
% 0.49/0.69                  ( k7_subset_1 @
% 0.49/0.69                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.49/0.69    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.49/0.69  thf('0', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69              (k1_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('1', plain,
% 0.49/0.69      (~
% 0.49/0.69       (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.69       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('split', [status(esa)], ['0'])).
% 0.49/0.69  thf('2', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('3', plain,
% 0.49/0.69      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('split', [status(esa)], ['2'])).
% 0.49/0.69  thf('4', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(t52_pre_topc, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.49/0.69             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.49/0.69               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.49/0.69  thf('5', plain,
% 0.49/0.69      (![X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.49/0.69          | ~ (v4_pre_topc @ X27 @ X28)
% 0.49/0.69          | ((k2_pre_topc @ X28 @ X27) = (X27))
% 0.49/0.69          | ~ (l1_pre_topc @ X28))),
% 0.49/0.69      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.49/0.69  thf('6', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.49/0.69        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.69  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('8', plain,
% 0.49/0.69      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('9', plain,
% 0.49/0.69      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.49/0.69         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['3', '8'])).
% 0.49/0.69  thf('10', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(l78_tops_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( k2_tops_1 @ A @ B ) =
% 0.49/0.69             ( k7_subset_1 @
% 0.49/0.69               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.49/0.69               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.49/0.69  thf('11', plain,
% 0.49/0.69      (![X33 : $i, X34 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.49/0.69          | ((k2_tops_1 @ X34 @ X33)
% 0.49/0.69              = (k7_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.49/0.69                 (k2_pre_topc @ X34 @ X33) @ (k1_tops_1 @ X34 @ X33)))
% 0.49/0.69          | ~ (l1_pre_topc @ X34))),
% 0.49/0.69      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.49/0.69  thf('12', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.69               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.69  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('14', plain,
% 0.49/0.69      (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.49/0.69            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.69  thf('15', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['9', '14'])).
% 0.49/0.69  thf('16', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(redefinition_k7_subset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.69       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.49/0.69  thf('17', plain,
% 0.49/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.49/0.69          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.49/0.69  thf('18', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf('19', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['15', '18'])).
% 0.49/0.69  thf('20', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf('21', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69              (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('split', [status(esa)], ['0'])).
% 0.49/0.69  thf('22', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.69  thf('23', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.49/0.69             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['19', '22'])).
% 0.49/0.69  thf('24', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.69       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.49/0.69  thf('25', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.69       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('split', [status(esa)], ['2'])).
% 0.49/0.69  thf('26', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf('27', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('split', [status(esa)], ['2'])).
% 0.49/0.69  thf('28', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.69  thf(t36_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.69  thf('29', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.49/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.69  thf(t3_subset, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.69  thf('30', plain,
% 0.49/0.69      (![X24 : $i, X26 : $i]:
% 0.49/0.69         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.69  thf('31', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.69  thf('32', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['28', '31'])).
% 0.49/0.69  thf(d5_subset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.49/0.69  thf('33', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i]:
% 0.49/0.69         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.49/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.49/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.49/0.69  thf('34', plain,
% 0.49/0.69      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.69  thf(t48_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.69  thf('35', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.49/0.69           = (k3_xboole_0 @ X12 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('36', plain,
% 0.49/0.69      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['34', '35'])).
% 0.49/0.69  thf('37', plain,
% 0.49/0.69      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.69  thf('38', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.69  thf('39', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i]:
% 0.49/0.69         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.49/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.49/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.49/0.69  thf('40', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.49/0.69           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.49/0.69  thf('41', plain,
% 0.49/0.69      ((((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ 
% 0.49/0.69             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['37', '40'])).
% 0.49/0.69  thf('42', plain,
% 0.49/0.69      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.69  thf('43', plain,
% 0.49/0.69      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ 
% 0.49/0.69             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('44', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['28', '31'])).
% 0.49/0.69  thf(involutiveness_k3_subset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.69       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.49/0.69  thf('45', plain,
% 0.49/0.69      (![X16 : $i, X17 : $i]:
% 0.49/0.69         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.49/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.49/0.69      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.49/0.69  thf('46', plain,
% 0.49/0.69      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.69  thf('47', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ 
% 0.49/0.69             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('demod', [status(thm)], ['43', '46'])).
% 0.49/0.69  thf('48', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['36', '47'])).
% 0.49/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.69  thf('49', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.69  thf(t100_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.69  thf('50', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X2 @ X3)
% 0.49/0.69           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.69  thf('51', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.49/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['49', '50'])).
% 0.49/0.69  thf('52', plain,
% 0.49/0.69      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.49/0.69             (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['48', '51'])).
% 0.49/0.69  thf('53', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.49/0.69           = (k3_xboole_0 @ X12 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('54', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.49/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.69  thf(t12_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.49/0.69  thf('55', plain,
% 0.49/0.69      (![X4 : $i, X5 : $i]:
% 0.49/0.69         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.49/0.69  thf('56', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['54', '55'])).
% 0.49/0.69  thf(t1_boole, axiom,
% 0.49/0.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.69  thf('57', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.49/0.69  thf('58', plain,
% 0.49/0.69      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['56', '57'])).
% 0.49/0.69  thf('59', plain,
% 0.49/0.69      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['53', '58'])).
% 0.49/0.69  thf('60', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.69  thf('61', plain,
% 0.49/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['59', '60'])).
% 0.49/0.69  thf('62', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.49/0.69           = (k3_xboole_0 @ X12 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('63', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.69  thf('64', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.49/0.69      inference('sup+', [status(thm)], ['62', '63'])).
% 0.49/0.69  thf('65', plain,
% 0.49/0.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['61', '64'])).
% 0.49/0.69  thf('66', plain,
% 0.49/0.69      (![X16 : $i, X17 : $i]:
% 0.49/0.69         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.49/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.49/0.69      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.49/0.69  thf('67', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.69  thf('68', plain,
% 0.49/0.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['61', '64'])).
% 0.49/0.69  thf('69', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i]:
% 0.49/0.69         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.49/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.49/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.49/0.69  thf('70', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['68', '69'])).
% 0.49/0.69  thf(t3_boole, axiom,
% 0.49/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.69  thf('71', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.69  thf('72', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['70', '71'])).
% 0.49/0.69  thf('73', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.69      inference('demod', [status(thm)], ['67', '72'])).
% 0.49/0.69  thf('74', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.69  thf('75', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.49/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.69  thf('76', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.69      inference('sup+', [status(thm)], ['74', '75'])).
% 0.49/0.69  thf('77', plain,
% 0.49/0.69      (![X24 : $i, X26 : $i]:
% 0.49/0.69         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.69  thf('78', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['76', '77'])).
% 0.49/0.69  thf('79', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i]:
% 0.49/0.69         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.49/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.49/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.49/0.69  thf('80', plain,
% 0.49/0.69      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.69  thf('81', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X2 @ X3)
% 0.49/0.69           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.69  thf('82', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k3_subset_1 @ X0 @ X0)
% 0.49/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['80', '81'])).
% 0.49/0.69  thf('83', plain,
% 0.49/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['59', '60'])).
% 0.49/0.69  thf('84', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.49/0.69           = (k3_xboole_0 @ X12 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('85', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.49/0.69           = (k3_xboole_0 @ X12 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('86', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.69           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['84', '85'])).
% 0.49/0.69  thf('87', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.49/0.69           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['83', '86'])).
% 0.49/0.69  thf('88', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.69  thf('89', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.69  thf('90', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.49/0.69      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.49/0.69  thf('91', plain,
% 0.49/0.69      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.69      inference('demod', [status(thm)], ['82', '90'])).
% 0.49/0.69  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.69      inference('demod', [status(thm)], ['73', '91'])).
% 0.49/0.69  thf('93', plain,
% 0.49/0.69      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('demod', [status(thm)], ['52', '92'])).
% 0.49/0.69  thf(t39_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.69  thf('94', plain,
% 0.49/0.69      (![X9 : $i, X10 : $i]:
% 0.49/0.69         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.49/0.69           = (k2_xboole_0 @ X9 @ X10))),
% 0.49/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.49/0.69  thf('95', plain,
% 0.49/0.69      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.49/0.69          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['93', '94'])).
% 0.49/0.69  thf('96', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.49/0.69  thf('97', plain,
% 0.49/0.69      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('demod', [status(thm)], ['95', '96'])).
% 0.49/0.69  thf('98', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(dt_k2_tops_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( l1_pre_topc @ A ) & 
% 0.49/0.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.69       ( m1_subset_1 @
% 0.49/0.69         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.49/0.69  thf('99', plain,
% 0.49/0.69      (![X29 : $i, X30 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X29)
% 0.49/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.49/0.69          | (m1_subset_1 @ (k2_tops_1 @ X29 @ X30) @ 
% 0.49/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.49/0.69      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.49/0.69  thf('100', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.49/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.69        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['98', '99'])).
% 0.49/0.69  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('102', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.49/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['100', '101'])).
% 0.49/0.69  thf('103', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(redefinition_k4_subset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.49/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.69       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.49/0.69  thf('104', plain,
% 0.49/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.49/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.49/0.69          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.49/0.69  thf('105', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69            = (k2_xboole_0 @ sk_B @ X0))
% 0.49/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['103', '104'])).
% 0.49/0.69  thf('106', plain,
% 0.49/0.69      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.49/0.69         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['102', '105'])).
% 0.49/0.69  thf('107', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(t65_tops_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( k2_pre_topc @ A @ B ) =
% 0.49/0.69             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.49/0.69  thf('108', plain,
% 0.49/0.69      (![X35 : $i, X36 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.49/0.69          | ((k2_pre_topc @ X36 @ X35)
% 0.49/0.69              = (k4_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.49/0.69                 (k2_tops_1 @ X36 @ X35)))
% 0.49/0.69          | ~ (l1_pre_topc @ X36))),
% 0.49/0.69      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.49/0.69  thf('109', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.49/0.69            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['107', '108'])).
% 0.49/0.69  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('111', plain,
% 0.49/0.69      (((k2_pre_topc @ sk_A @ sk_B)
% 0.49/0.69         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['109', '110'])).
% 0.49/0.69  thf('112', plain,
% 0.49/0.69      (((k2_pre_topc @ sk_A @ sk_B)
% 0.49/0.69         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['106', '111'])).
% 0.49/0.69  thf('113', plain,
% 0.49/0.69      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['97', '112'])).
% 0.49/0.69  thf('114', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(fc1_tops_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.49/0.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.69       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.49/0.69  thf('115', plain,
% 0.49/0.69      (![X31 : $i, X32 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X31)
% 0.49/0.69          | ~ (v2_pre_topc @ X31)
% 0.49/0.69          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.49/0.69          | (v4_pre_topc @ (k2_pre_topc @ X31 @ X32) @ X31))),
% 0.49/0.69      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.49/0.69  thf('116', plain,
% 0.49/0.69      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.49/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.69        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['114', '115'])).
% 0.49/0.69  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('119', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.49/0.69  thf('120', plain,
% 0.49/0.69      (((v4_pre_topc @ sk_B @ sk_A))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['113', '119'])).
% 0.49/0.69  thf('121', plain,
% 0.49/0.69      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('split', [status(esa)], ['0'])).
% 0.49/0.69  thf('122', plain,
% 0.49/0.69      (~
% 0.49/0.69       (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.69       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['120', '121'])).
% 0.49/0.69  thf('123', plain, ($false),
% 0.49/0.69      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '122'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
