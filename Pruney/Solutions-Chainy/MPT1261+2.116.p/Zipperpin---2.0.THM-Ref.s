%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cDDNy9oGtc

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:55 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 604 expanded)
%              Number of leaves         :   35 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          : 1516 (7697 expanded)
%              Number of equality atoms :  112 ( 462 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X31 @ X30 ) @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_subset_1 @ X17 @ X18 @ ( k3_subset_1 @ X17 @ X18 ) )
        = ( k2_subset_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('53',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_subset_1 @ X17 @ X18 @ ( k3_subset_1 @ X17 @ X18 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','56'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('77',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','56'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','80','99'])).

thf('101',plain,
    ( ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','80','99'])).

thf('103',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('104',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('106',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('107',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cDDNy9oGtc
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:08:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.99/2.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.99/2.25  % Solved by: fo/fo7.sh
% 1.99/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.99/2.25  % done 1976 iterations in 1.781s
% 1.99/2.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.99/2.25  % SZS output start Refutation
% 1.99/2.25  thf(sk_A_type, type, sk_A: $i).
% 1.99/2.25  thf(sk_B_type, type, sk_B: $i).
% 1.99/2.25  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.99/2.25  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.99/2.25  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.99/2.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.99/2.25  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.99/2.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.99/2.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.99/2.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.99/2.25  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.99/2.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.99/2.25  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.99/2.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.08/2.25  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.08/2.25  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.08/2.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.08/2.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.08/2.25  thf(t77_tops_1, conjecture,
% 2.08/2.25    (![A:$i]:
% 2.08/2.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.08/2.25       ( ![B:$i]:
% 2.08/2.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.08/2.25           ( ( v4_pre_topc @ B @ A ) <=>
% 2.08/2.25             ( ( k2_tops_1 @ A @ B ) =
% 2.08/2.25               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 2.08/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.08/2.25    (~( ![A:$i]:
% 2.08/2.25        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.08/2.25          ( ![B:$i]:
% 2.08/2.25            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.08/2.25              ( ( v4_pre_topc @ B @ A ) <=>
% 2.08/2.25                ( ( k2_tops_1 @ A @ B ) =
% 2.08/2.25                  ( k7_subset_1 @
% 2.08/2.25                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 2.08/2.25    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 2.08/2.25  thf('0', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25              (k1_tops_1 @ sk_A @ sk_B)))
% 2.08/2.25        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('1', plain,
% 2.08/2.25      (~
% 2.08/2.25       (((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.08/2.25       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('split', [status(esa)], ['0'])).
% 2.08/2.25  thf('2', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B)))
% 2.08/2.25        | (v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('3', plain,
% 2.08/2.25      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.08/2.25      inference('split', [status(esa)], ['2'])).
% 2.08/2.25  thf('4', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf(t52_pre_topc, axiom,
% 2.08/2.25    (![A:$i]:
% 2.08/2.25     ( ( l1_pre_topc @ A ) =>
% 2.08/2.25       ( ![B:$i]:
% 2.08/2.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.08/2.25           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 2.08/2.25             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 2.08/2.25               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.08/2.25  thf('5', plain,
% 2.08/2.25      (![X22 : $i, X23 : $i]:
% 2.08/2.25         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.08/2.25          | ~ (v4_pre_topc @ X22 @ X23)
% 2.08/2.25          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 2.08/2.25          | ~ (l1_pre_topc @ X23))),
% 2.08/2.25      inference('cnf', [status(esa)], [t52_pre_topc])).
% 2.08/2.25  thf('6', plain,
% 2.08/2.25      ((~ (l1_pre_topc @ sk_A)
% 2.08/2.25        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 2.08/2.25        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('sup-', [status(thm)], ['4', '5'])).
% 2.08/2.25  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('8', plain,
% 2.08/2.25      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('demod', [status(thm)], ['6', '7'])).
% 2.08/2.25  thf('9', plain,
% 2.08/2.25      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.08/2.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.08/2.25      inference('sup-', [status(thm)], ['3', '8'])).
% 2.08/2.25  thf('10', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf(l78_tops_1, axiom,
% 2.08/2.25    (![A:$i]:
% 2.08/2.25     ( ( l1_pre_topc @ A ) =>
% 2.08/2.25       ( ![B:$i]:
% 2.08/2.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.08/2.25           ( ( k2_tops_1 @ A @ B ) =
% 2.08/2.25             ( k7_subset_1 @
% 2.08/2.25               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.08/2.25               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.08/2.25  thf('11', plain,
% 2.08/2.25      (![X28 : $i, X29 : $i]:
% 2.08/2.25         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.08/2.25          | ((k2_tops_1 @ X29 @ X28)
% 2.08/2.25              = (k7_subset_1 @ (u1_struct_0 @ X29) @ 
% 2.08/2.25                 (k2_pre_topc @ X29 @ X28) @ (k1_tops_1 @ X29 @ X28)))
% 2.08/2.25          | ~ (l1_pre_topc @ X29))),
% 2.08/2.25      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.08/2.25  thf('12', plain,
% 2.08/2.25      ((~ (l1_pre_topc @ sk_A)
% 2.08/2.25        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.08/2.25               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.08/2.25      inference('sup-', [status(thm)], ['10', '11'])).
% 2.08/2.25  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('14', plain,
% 2.08/2.25      (((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.08/2.25            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.08/2.25      inference('demod', [status(thm)], ['12', '13'])).
% 2.08/2.25  thf('15', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['9', '14'])).
% 2.08/2.25  thf('16', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf(redefinition_k7_subset_1, axiom,
% 2.08/2.25    (![A:$i,B:$i,C:$i]:
% 2.08/2.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.08/2.25       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.08/2.25  thf('17', plain,
% 2.08/2.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.08/2.25         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 2.08/2.25          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 2.08/2.25      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.08/2.25  thf('18', plain,
% 2.08/2.25      (![X0 : $i]:
% 2.08/2.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.08/2.25           = (k4_xboole_0 @ sk_B @ X0))),
% 2.08/2.25      inference('sup-', [status(thm)], ['16', '17'])).
% 2.08/2.25  thf('19', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.08/2.25      inference('demod', [status(thm)], ['15', '18'])).
% 2.08/2.25  thf('20', plain,
% 2.08/2.25      (![X0 : $i]:
% 2.08/2.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.08/2.25           = (k4_xboole_0 @ sk_B @ X0))),
% 2.08/2.25      inference('sup-', [status(thm)], ['16', '17'])).
% 2.08/2.25  thf('21', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25              (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= (~
% 2.08/2.25             (((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('split', [status(esa)], ['0'])).
% 2.08/2.25  thf('22', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= (~
% 2.08/2.25             (((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup-', [status(thm)], ['20', '21'])).
% 2.08/2.25  thf('23', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 2.08/2.25         <= (~
% 2.08/2.25             (((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 2.08/2.25             ((v4_pre_topc @ sk_B @ sk_A)))),
% 2.08/2.25      inference('sup-', [status(thm)], ['19', '22'])).
% 2.08/2.25  thf('24', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.08/2.25       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('simplify', [status(thm)], ['23'])).
% 2.08/2.25  thf('25', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.08/2.25       ((v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('split', [status(esa)], ['2'])).
% 2.08/2.25  thf(idempotence_k2_xboole_0, axiom,
% 2.08/2.25    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.08/2.25  thf('26', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 2.08/2.25      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.08/2.25  thf('27', plain,
% 2.08/2.25      (![X0 : $i]:
% 2.08/2.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.08/2.25           = (k4_xboole_0 @ sk_B @ X0))),
% 2.08/2.25      inference('sup-', [status(thm)], ['16', '17'])).
% 2.08/2.25  thf('28', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('split', [status(esa)], ['2'])).
% 2.08/2.25  thf('29', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['27', '28'])).
% 2.08/2.25  thf(t36_xboole_1, axiom,
% 2.08/2.25    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.08/2.25  thf('30', plain,
% 2.08/2.25      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 2.08/2.25      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.08/2.25  thf(t3_subset, axiom,
% 2.08/2.25    (![A:$i,B:$i]:
% 2.08/2.25     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.08/2.25  thf('31', plain,
% 2.08/2.25      (![X19 : $i, X21 : $i]:
% 2.08/2.25         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 2.08/2.25      inference('cnf', [status(esa)], [t3_subset])).
% 2.08/2.25  thf('32', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]:
% 2.08/2.25         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.08/2.25      inference('sup-', [status(thm)], ['30', '31'])).
% 2.08/2.25  thf('33', plain,
% 2.08/2.25      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['29', '32'])).
% 2.08/2.25  thf('34', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf(t44_tops_1, axiom,
% 2.08/2.25    (![A:$i]:
% 2.08/2.25     ( ( l1_pre_topc @ A ) =>
% 2.08/2.25       ( ![B:$i]:
% 2.08/2.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.08/2.25           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.08/2.25  thf('35', plain,
% 2.08/2.25      (![X30 : $i, X31 : $i]:
% 2.08/2.25         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.08/2.25          | (r1_tarski @ (k1_tops_1 @ X31 @ X30) @ X30)
% 2.08/2.25          | ~ (l1_pre_topc @ X31))),
% 2.08/2.25      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.08/2.25  thf('36', plain,
% 2.08/2.25      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.08/2.25      inference('sup-', [status(thm)], ['34', '35'])).
% 2.08/2.25  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('38', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.08/2.25      inference('demod', [status(thm)], ['36', '37'])).
% 2.08/2.25  thf('39', plain,
% 2.08/2.25      (![X19 : $i, X21 : $i]:
% 2.08/2.25         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 2.08/2.25      inference('cnf', [status(esa)], [t3_subset])).
% 2.08/2.25  thf('40', plain,
% 2.08/2.25      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 2.08/2.25      inference('sup-', [status(thm)], ['38', '39'])).
% 2.08/2.25  thf(redefinition_k4_subset_1, axiom,
% 2.08/2.25    (![A:$i,B:$i,C:$i]:
% 2.08/2.25     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.08/2.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.08/2.25       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.08/2.25  thf('41', plain,
% 2.08/2.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.08/2.25         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 2.08/2.25          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 2.08/2.25          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 2.08/2.25      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.08/2.25  thf('42', plain,
% 2.08/2.25      (![X0 : $i]:
% 2.08/2.25         (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.08/2.25            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 2.08/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 2.08/2.25      inference('sup-', [status(thm)], ['40', '41'])).
% 2.08/2.25  thf('43', plain,
% 2.08/2.25      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25          (k2_tops_1 @ sk_A @ sk_B))
% 2.08/2.25          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25             (k2_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup-', [status(thm)], ['33', '42'])).
% 2.08/2.25  thf(commutativity_k2_xboole_0, axiom,
% 2.08/2.25    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.08/2.25  thf('44', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.08/2.25      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.08/2.25  thf('45', plain,
% 2.08/2.25      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25          (k2_tops_1 @ sk_A @ sk_B))
% 2.08/2.25          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('demod', [status(thm)], ['43', '44'])).
% 2.08/2.25  thf('46', plain,
% 2.08/2.25      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 2.08/2.25      inference('sup-', [status(thm)], ['38', '39'])).
% 2.08/2.25  thf(d5_subset_1, axiom,
% 2.08/2.25    (![A:$i,B:$i]:
% 2.08/2.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.08/2.25       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.08/2.25  thf('47', plain,
% 2.08/2.25      (![X9 : $i, X10 : $i]:
% 2.08/2.25         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 2.08/2.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 2.08/2.25      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.08/2.25  thf('48', plain,
% 2.08/2.25      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.08/2.25         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.08/2.25      inference('sup-', [status(thm)], ['46', '47'])).
% 2.08/2.25  thf('49', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['27', '28'])).
% 2.08/2.25  thf('50', plain,
% 2.08/2.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['48', '49'])).
% 2.08/2.25  thf('51', plain,
% 2.08/2.25      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 2.08/2.25      inference('sup-', [status(thm)], ['38', '39'])).
% 2.08/2.25  thf(t25_subset_1, axiom,
% 2.08/2.25    (![A:$i,B:$i]:
% 2.08/2.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.08/2.25       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 2.08/2.25         ( k2_subset_1 @ A ) ) ))).
% 2.08/2.25  thf('52', plain,
% 2.08/2.25      (![X17 : $i, X18 : $i]:
% 2.08/2.25         (((k4_subset_1 @ X17 @ X18 @ (k3_subset_1 @ X17 @ X18))
% 2.08/2.25            = (k2_subset_1 @ X17))
% 2.08/2.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.08/2.25      inference('cnf', [status(esa)], [t25_subset_1])).
% 2.08/2.25  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.08/2.25  thf('53', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 2.08/2.25      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.08/2.25  thf('54', plain,
% 2.08/2.25      (![X17 : $i, X18 : $i]:
% 2.08/2.25         (((k4_subset_1 @ X17 @ X18 @ (k3_subset_1 @ X17 @ X18)) = (X17))
% 2.08/2.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.08/2.25      inference('demod', [status(thm)], ['52', '53'])).
% 2.08/2.25  thf('55', plain,
% 2.08/2.25      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25         (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 2.08/2.25      inference('sup-', [status(thm)], ['51', '54'])).
% 2.08/2.25  thf('56', plain,
% 2.08/2.25      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['50', '55'])).
% 2.08/2.25  thf('57', plain,
% 2.08/2.25      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 2.08/2.25          = (sk_B)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['45', '56'])).
% 2.08/2.25  thf(t4_xboole_1, axiom,
% 2.08/2.25    (![A:$i,B:$i,C:$i]:
% 2.08/2.25     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.08/2.25       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.08/2.25  thf('58', plain,
% 2.08/2.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 2.08/2.25           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 2.08/2.25      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.08/2.25  thf('59', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.08/2.25      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.08/2.25  thf('60', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 2.08/2.25           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['58', '59'])).
% 2.08/2.25  thf('61', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.08/2.25      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.08/2.25  thf('62', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 2.08/2.25      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.08/2.25  thf('63', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.08/2.25      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.08/2.25  thf('64', plain,
% 2.08/2.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 2.08/2.25           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 2.08/2.25      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.08/2.25  thf('65', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.08/2.25           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['63', '64'])).
% 2.08/2.25  thf('66', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X1 @ X0)
% 2.08/2.25           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['62', '65'])).
% 2.08/2.25  thf('67', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 2.08/2.25      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.08/2.25  thf('68', plain,
% 2.08/2.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 2.08/2.25           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 2.08/2.25      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.08/2.25  thf('69', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X0 @ X1)
% 2.08/2.25           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['67', '68'])).
% 2.08/2.25  thf('70', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X1 @ X0)
% 2.08/2.25           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.08/2.25      inference('demod', [status(thm)], ['66', '69'])).
% 2.08/2.25  thf('71', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X0 @ X1)
% 2.08/2.25           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['61', '70'])).
% 2.08/2.25  thf('72', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 2.08/2.25           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['60', '71'])).
% 2.08/2.25  thf('73', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.08/2.25           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['63', '64'])).
% 2.08/2.25  thf('74', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 2.08/2.25           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.08/2.25      inference('demod', [status(thm)], ['72', '73'])).
% 2.08/2.25  thf('75', plain,
% 2.08/2.25      ((![X0 : $i]:
% 2.08/2.25          ((k2_xboole_0 @ X0 @ 
% 2.08/2.25            (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25             (k2_tops_1 @ sk_A @ sk_B)))
% 2.08/2.25            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25               (k2_xboole_0 @ X0 @ sk_B))))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['57', '74'])).
% 2.08/2.25  thf('76', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.08/2.25      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.08/2.25  thf('77', plain,
% 2.08/2.25      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 2.08/2.25          = (sk_B)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['45', '56'])).
% 2.08/2.25  thf('78', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.08/2.25           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['63', '64'])).
% 2.08/2.25  thf('79', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.08/2.25      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.08/2.25  thf('80', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 2.08/2.25           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['78', '79'])).
% 2.08/2.25  thf('81', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf(dt_k2_tops_1, axiom,
% 2.08/2.25    (![A:$i,B:$i]:
% 2.08/2.25     ( ( ( l1_pre_topc @ A ) & 
% 2.08/2.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.08/2.25       ( m1_subset_1 @
% 2.08/2.25         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.08/2.25  thf('82', plain,
% 2.08/2.25      (![X24 : $i, X25 : $i]:
% 2.08/2.25         (~ (l1_pre_topc @ X24)
% 2.08/2.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.08/2.25          | (m1_subset_1 @ (k2_tops_1 @ X24 @ X25) @ 
% 2.08/2.25             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 2.08/2.25      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.08/2.25  thf('83', plain,
% 2.08/2.25      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.08/2.25        | ~ (l1_pre_topc @ sk_A))),
% 2.08/2.25      inference('sup-', [status(thm)], ['81', '82'])).
% 2.08/2.25  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('85', plain,
% 2.08/2.25      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('demod', [status(thm)], ['83', '84'])).
% 2.08/2.25  thf('86', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('87', plain,
% 2.08/2.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.08/2.25         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 2.08/2.25          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 2.08/2.25          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 2.08/2.25      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.08/2.25  thf('88', plain,
% 2.08/2.25      (![X0 : $i]:
% 2.08/2.25         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.08/2.25            = (k2_xboole_0 @ sk_B @ X0))
% 2.08/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.08/2.25      inference('sup-', [status(thm)], ['86', '87'])).
% 2.08/2.25  thf('89', plain,
% 2.08/2.25      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.08/2.25         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.08/2.25      inference('sup-', [status(thm)], ['85', '88'])).
% 2.08/2.25  thf('90', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf(t65_tops_1, axiom,
% 2.08/2.25    (![A:$i]:
% 2.08/2.25     ( ( l1_pre_topc @ A ) =>
% 2.08/2.25       ( ![B:$i]:
% 2.08/2.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.08/2.25           ( ( k2_pre_topc @ A @ B ) =
% 2.08/2.25             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.08/2.25  thf('91', plain,
% 2.08/2.25      (![X32 : $i, X33 : $i]:
% 2.08/2.25         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.08/2.25          | ((k2_pre_topc @ X33 @ X32)
% 2.08/2.25              = (k4_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 2.08/2.25                 (k2_tops_1 @ X33 @ X32)))
% 2.08/2.25          | ~ (l1_pre_topc @ X33))),
% 2.08/2.25      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.08/2.25  thf('92', plain,
% 2.08/2.25      ((~ (l1_pre_topc @ sk_A)
% 2.08/2.25        | ((k2_pre_topc @ sk_A @ sk_B)
% 2.08/2.25            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25               (k2_tops_1 @ sk_A @ sk_B))))),
% 2.08/2.25      inference('sup-', [status(thm)], ['90', '91'])).
% 2.08/2.25  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('94', plain,
% 2.08/2.25      (((k2_pre_topc @ sk_A @ sk_B)
% 2.08/2.25         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.08/2.25      inference('demod', [status(thm)], ['92', '93'])).
% 2.08/2.25  thf('95', plain,
% 2.08/2.25      (((k2_pre_topc @ sk_A @ sk_B)
% 2.08/2.25         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['89', '94'])).
% 2.08/2.25  thf('96', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.08/2.25           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['63', '64'])).
% 2.08/2.25  thf('97', plain,
% 2.08/2.25      (![X0 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 2.08/2.25           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.08/2.25              (k2_xboole_0 @ sk_B @ X0)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['95', '96'])).
% 2.08/2.25  thf('98', plain,
% 2.08/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 2.08/2.25           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.08/2.25      inference('sup+', [status(thm)], ['58', '59'])).
% 2.08/2.25  thf('99', plain,
% 2.08/2.25      (![X0 : $i]:
% 2.08/2.25         ((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 2.08/2.25           = (k2_xboole_0 @ sk_B @ 
% 2.08/2.25              (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.08/2.25      inference('demod', [status(thm)], ['97', '98'])).
% 2.08/2.25  thf('100', plain,
% 2.08/2.25      ((![X0 : $i]:
% 2.08/2.25          ((k2_xboole_0 @ X0 @ sk_B)
% 2.08/2.25            = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('demod', [status(thm)], ['75', '76', '77', '80', '99'])).
% 2.08/2.25  thf('101', plain,
% 2.08/2.25      ((((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 2.08/2.25          = (k2_pre_topc @ sk_A @ sk_B)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['26', '100'])).
% 2.08/2.25  thf('102', plain,
% 2.08/2.25      ((![X0 : $i]:
% 2.08/2.25          ((k2_xboole_0 @ X0 @ sk_B)
% 2.08/2.25            = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('demod', [status(thm)], ['75', '76', '77', '80', '99'])).
% 2.08/2.25  thf('103', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 2.08/2.25      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.08/2.25  thf('104', plain,
% 2.08/2.25      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('demod', [status(thm)], ['101', '102', '103'])).
% 2.08/2.25  thf('105', plain,
% 2.08/2.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf(fc1_tops_1, axiom,
% 2.08/2.25    (![A:$i,B:$i]:
% 2.08/2.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.08/2.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.08/2.25       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 2.08/2.25  thf('106', plain,
% 2.08/2.25      (![X26 : $i, X27 : $i]:
% 2.08/2.25         (~ (l1_pre_topc @ X26)
% 2.08/2.25          | ~ (v2_pre_topc @ X26)
% 2.08/2.25          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 2.08/2.25          | (v4_pre_topc @ (k2_pre_topc @ X26 @ X27) @ X26))),
% 2.08/2.25      inference('cnf', [status(esa)], [fc1_tops_1])).
% 2.08/2.25  thf('107', plain,
% 2.08/2.25      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.08/2.25        | ~ (v2_pre_topc @ sk_A)
% 2.08/2.25        | ~ (l1_pre_topc @ sk_A))),
% 2.08/2.25      inference('sup-', [status(thm)], ['105', '106'])).
% 2.08/2.25  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 2.08/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.25  thf('110', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.08/2.25      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.08/2.25  thf('111', plain,
% 2.08/2.25      (((v4_pre_topc @ sk_B @ sk_A))
% 2.08/2.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.08/2.25      inference('sup+', [status(thm)], ['104', '110'])).
% 2.08/2.25  thf('112', plain,
% 2.08/2.25      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 2.08/2.25      inference('split', [status(esa)], ['0'])).
% 2.08/2.25  thf('113', plain,
% 2.08/2.25      (~
% 2.08/2.25       (((k2_tops_1 @ sk_A @ sk_B)
% 2.08/2.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.08/2.25             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.08/2.25       ((v4_pre_topc @ sk_B @ sk_A))),
% 2.08/2.25      inference('sup-', [status(thm)], ['111', '112'])).
% 2.08/2.25  thf('114', plain, ($false),
% 2.08/2.25      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '113'])).
% 2.08/2.25  
% 2.08/2.25  % SZS output end Refutation
% 2.08/2.25  
% 2.08/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
