%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d7zibING11

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:45 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 309 expanded)
%              Number of leaves         :   43 ( 107 expanded)
%              Depth                    :   18
%              Number of atoms          : 1537 (3584 expanded)
%              Number of equality atoms :  127 ( 243 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v4_pre_topc @ X32 @ X33 )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_tops_1 @ X39 @ X38 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ X38 ) @ ( k1_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,
    ( ( ( k3_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','61'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('63',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('81',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('84',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','79','84'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('87',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('91',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('95',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('96',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('100',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('104',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_pre_topc @ X41 @ X40 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( k2_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('111',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X36 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('112',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['109','115'])).

thf('117',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d7zibING11
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.99  % Solved by: fo/fo7.sh
% 0.78/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.99  % done 1789 iterations in 0.532s
% 0.78/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.99  % SZS output start Refutation
% 0.78/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.78/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.99  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.78/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.78/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.78/0.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.78/0.99  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.78/0.99  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.78/0.99  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.78/0.99  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.78/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.99  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.78/0.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.78/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(t77_tops_1, conjecture,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.78/0.99       ( ![B:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.99           ( ( v4_pre_topc @ B @ A ) <=>
% 0.78/0.99             ( ( k2_tops_1 @ A @ B ) =
% 0.78/0.99               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.78/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.99    (~( ![A:$i]:
% 0.78/0.99        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.78/0.99          ( ![B:$i]:
% 0.78/0.99            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.99              ( ( v4_pre_topc @ B @ A ) <=>
% 0.78/0.99                ( ( k2_tops_1 @ A @ B ) =
% 0.78/0.99                  ( k7_subset_1 @
% 0.78/0.99                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.78/0.99    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.78/0.99  thf('0', plain,
% 0.78/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/0.99          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/0.99              (k1_tops_1 @ sk_A @ sk_B)))
% 0.78/0.99        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('1', plain,
% 0.78/0.99      (~
% 0.78/0.99       (((k2_tops_1 @ sk_A @ sk_B)
% 0.78/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.78/0.99       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.78/0.99      inference('split', [status(esa)], ['0'])).
% 0.78/0.99  thf('2', plain,
% 0.78/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/0.99             (k1_tops_1 @ sk_A @ sk_B)))
% 0.78/0.99        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('3', plain,
% 0.78/0.99      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.78/0.99      inference('split', [status(esa)], ['2'])).
% 0.78/0.99  thf('4', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(t52_pre_topc, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( l1_pre_topc @ A ) =>
% 0.78/0.99       ( ![B:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.99           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.78/0.99             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.78/0.99               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.78/0.99  thf('5', plain,
% 0.78/0.99      (![X32 : $i, X33 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.78/0.99          | ~ (v4_pre_topc @ X32 @ X33)
% 0.78/0.99          | ((k2_pre_topc @ X33 @ X32) = (X32))
% 0.78/0.99          | ~ (l1_pre_topc @ X33))),
% 0.78/0.99      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.78/0.99  thf('6', plain,
% 0.78/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.78/0.99        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.78/0.99        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.78/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.78/0.99  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('8', plain,
% 0.78/0.99      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['6', '7'])).
% 0.78/0.99  thf('9', plain,
% 0.78/0.99      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.78/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['3', '8'])).
% 0.78/0.99  thf('10', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(l78_tops_1, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( l1_pre_topc @ A ) =>
% 0.78/0.99       ( ![B:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.99           ( ( k2_tops_1 @ A @ B ) =
% 0.78/0.99             ( k7_subset_1 @
% 0.78/0.99               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.78/0.99               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.78/0.99  thf('11', plain,
% 0.78/0.99      (![X38 : $i, X39 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.78/0.99          | ((k2_tops_1 @ X39 @ X38)
% 0.78/0.99              = (k7_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.78/1.00                 (k2_pre_topc @ X39 @ X38) @ (k1_tops_1 @ X39 @ X38)))
% 0.78/1.00          | ~ (l1_pre_topc @ X39))),
% 0.78/1.00      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.78/1.00  thf('12', plain,
% 0.78/1.00      ((~ (l1_pre_topc @ sk_A)
% 0.78/1.00        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.00               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.78/1.00  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf('14', plain,
% 0.78/1.00      (((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.78/1.00            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.78/1.00      inference('demod', [status(thm)], ['12', '13'])).
% 0.78/1.00  thf('15', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00             (k1_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.78/1.00      inference('sup+', [status(thm)], ['9', '14'])).
% 0.78/1.00  thf('16', plain,
% 0.78/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf(redefinition_k7_subset_1, axiom,
% 0.78/1.00    (![A:$i,B:$i,C:$i]:
% 0.78/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/1.00       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.78/1.00  thf('17', plain,
% 0.78/1.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.78/1.00         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.78/1.00          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 0.78/1.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.78/1.00  thf('18', plain,
% 0.78/1.00      (![X0 : $i]:
% 0.78/1.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.78/1.00           = (k4_xboole_0 @ sk_B @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['16', '17'])).
% 0.78/1.00  thf('19', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.78/1.00      inference('demod', [status(thm)], ['15', '18'])).
% 0.78/1.00  thf('20', plain,
% 0.78/1.00      (![X0 : $i]:
% 0.78/1.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.78/1.00           = (k4_xboole_0 @ sk_B @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['16', '17'])).
% 0.78/1.00  thf('21', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00              (k1_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= (~
% 0.78/1.00             (((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('split', [status(esa)], ['0'])).
% 0.78/1.00  thf('22', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= (~
% 0.78/1.00             (((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['20', '21'])).
% 0.78/1.00  thf('23', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.78/1.00         <= (~
% 0.78/1.00             (((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.78/1.00             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.78/1.00      inference('sup-', [status(thm)], ['19', '22'])).
% 0.78/1.00  thf('24', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.78/1.00       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.78/1.00      inference('simplify', [status(thm)], ['23'])).
% 0.78/1.00  thf('25', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.78/1.00       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.78/1.00      inference('split', [status(esa)], ['2'])).
% 0.78/1.00  thf('26', plain,
% 0.78/1.00      (![X0 : $i]:
% 0.78/1.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.78/1.00           = (k4_xboole_0 @ sk_B @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['16', '17'])).
% 0.78/1.00  thf('27', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00             (k1_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('split', [status(esa)], ['2'])).
% 0.78/1.00  thf('28', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['26', '27'])).
% 0.78/1.00  thf(t36_xboole_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.78/1.00  thf('29', plain,
% 0.78/1.00      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.78/1.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/1.00  thf(t3_subset, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.78/1.00  thf('30', plain,
% 0.78/1.00      (![X29 : $i, X31 : $i]:
% 0.78/1.00         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X29 @ X31))),
% 0.78/1.00      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.00  thf('31', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.78/1.00  thf('32', plain,
% 0.78/1.00      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['28', '31'])).
% 0.78/1.00  thf(d5_subset_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/1.00       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.78/1.00  thf('33', plain,
% 0.78/1.00      (![X17 : $i, X18 : $i]:
% 0.78/1.00         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.78/1.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.78/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/1.00  thf('34', plain,
% 0.78/1.00      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/1.00  thf(t48_xboole_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.78/1.00  thf('35', plain,
% 0.78/1.00      (![X9 : $i, X10 : $i]:
% 0.78/1.00         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.78/1.00           = (k3_xboole_0 @ X9 @ X10))),
% 0.78/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/1.00  thf('36', plain,
% 0.78/1.00      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.78/1.00          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['34', '35'])).
% 0.78/1.00  thf('37', plain,
% 0.78/1.00      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/1.00  thf('38', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.78/1.00  thf('39', plain,
% 0.78/1.00      (![X17 : $i, X18 : $i]:
% 0.78/1.00         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.78/1.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.78/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/1.00  thf('40', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.78/1.00           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.78/1.00      inference('sup-', [status(thm)], ['38', '39'])).
% 0.78/1.00  thf('41', plain,
% 0.78/1.00      ((((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ 
% 0.78/1.00             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['37', '40'])).
% 0.78/1.00  thf('42', plain,
% 0.78/1.00      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/1.00  thf('43', plain,
% 0.78/1.00      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ 
% 0.78/1.00             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('demod', [status(thm)], ['41', '42'])).
% 0.78/1.00  thf('44', plain,
% 0.78/1.00      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['28', '31'])).
% 0.78/1.00  thf(involutiveness_k3_subset_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/1.00       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.78/1.00  thf('45', plain,
% 0.78/1.00      (![X19 : $i, X20 : $i]:
% 0.78/1.00         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.78/1.00          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.78/1.00      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.78/1.00  thf('46', plain,
% 0.78/1.00      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.78/1.00          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['44', '45'])).
% 0.78/1.00  thf('47', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k4_xboole_0 @ sk_B @ 
% 0.78/1.00             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('demod', [status(thm)], ['43', '46'])).
% 0.78/1.00  thf('48', plain,
% 0.78/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['36', '47'])).
% 0.78/1.00  thf(commutativity_k2_tarski, axiom,
% 0.78/1.00    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.78/1.00  thf('49', plain,
% 0.78/1.00      (![X13 : $i, X14 : $i]:
% 0.78/1.00         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.78/1.00      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.78/1.00  thf(t12_setfam_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.78/1.00  thf('50', plain,
% 0.78/1.00      (![X27 : $i, X28 : $i]:
% 0.78/1.00         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.78/1.00      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.78/1.00  thf('51', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/1.00      inference('sup+', [status(thm)], ['49', '50'])).
% 0.78/1.00  thf('52', plain,
% 0.78/1.00      (![X27 : $i, X28 : $i]:
% 0.78/1.00         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.78/1.00      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.78/1.00  thf('53', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/1.00      inference('sup+', [status(thm)], ['51', '52'])).
% 0.78/1.00  thf('54', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.78/1.00  thf('55', plain,
% 0.78/1.00      (![X19 : $i, X20 : $i]:
% 0.78/1.00         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.78/1.00          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.78/1.00      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.78/1.00  thf('56', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.78/1.00           = (k4_xboole_0 @ X0 @ X1))),
% 0.78/1.00      inference('sup-', [status(thm)], ['54', '55'])).
% 0.78/1.00  thf('57', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.78/1.00           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.78/1.00      inference('sup-', [status(thm)], ['38', '39'])).
% 0.78/1.00  thf('58', plain,
% 0.78/1.00      (![X9 : $i, X10 : $i]:
% 0.78/1.00         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.78/1.00           = (k3_xboole_0 @ X9 @ X10))),
% 0.78/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/1.00  thf('59', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.78/1.00           = (k3_xboole_0 @ X1 @ X0))),
% 0.78/1.00      inference('sup+', [status(thm)], ['57', '58'])).
% 0.78/1.00  thf('60', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.78/1.00           = (k4_xboole_0 @ X0 @ X1))),
% 0.78/1.00      inference('demod', [status(thm)], ['56', '59'])).
% 0.78/1.00  thf('61', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.78/1.00           = (k4_xboole_0 @ X0 @ X1))),
% 0.78/1.00      inference('sup+', [status(thm)], ['53', '60'])).
% 0.78/1.00  thf('62', plain,
% 0.78/1.00      ((((k3_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.78/1.00          = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['48', '61'])).
% 0.78/1.00  thf(t3_boole, axiom,
% 0.78/1.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.78/1.00  thf('63', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.78/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.78/1.00  thf('64', plain,
% 0.78/1.00      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.78/1.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/1.00  thf('65', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.78/1.00      inference('sup+', [status(thm)], ['63', '64'])).
% 0.78/1.00  thf('66', plain,
% 0.78/1.00      (![X29 : $i, X31 : $i]:
% 0.78/1.00         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X29 @ X31))),
% 0.78/1.00      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.00  thf('67', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['65', '66'])).
% 0.78/1.00  thf('68', plain,
% 0.78/1.00      (![X17 : $i, X18 : $i]:
% 0.78/1.00         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.78/1.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.78/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/1.00  thf('69', plain,
% 0.78/1.00      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['67', '68'])).
% 0.78/1.00  thf(idempotence_k2_xboole_0, axiom,
% 0.78/1.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/1.00  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.78/1.00      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.78/1.00  thf(t46_xboole_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.78/1.00  thf('71', plain,
% 0.78/1.00      (![X7 : $i, X8 : $i]:
% 0.78/1.00         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.78/1.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.78/1.00  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/1.00      inference('sup+', [status(thm)], ['70', '71'])).
% 0.78/1.00  thf('73', plain,
% 0.78/1.00      (![X9 : $i, X10 : $i]:
% 0.78/1.00         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.78/1.00           = (k3_xboole_0 @ X9 @ X10))),
% 0.78/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/1.00  thf('74', plain,
% 0.78/1.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.78/1.00      inference('sup+', [status(thm)], ['72', '73'])).
% 0.78/1.00  thf('75', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.78/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.78/1.00  thf('76', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.78/1.00      inference('demod', [status(thm)], ['74', '75'])).
% 0.78/1.00  thf(t100_xboole_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/1.00  thf('77', plain,
% 0.78/1.00      (![X1 : $i, X2 : $i]:
% 0.78/1.00         ((k4_xboole_0 @ X1 @ X2)
% 0.78/1.00           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.78/1.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/1.00  thf('78', plain,
% 0.78/1.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/1.00      inference('sup+', [status(thm)], ['76', '77'])).
% 0.78/1.00  thf('79', plain,
% 0.78/1.00      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/1.00      inference('sup+', [status(thm)], ['69', '78'])).
% 0.78/1.00  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/1.00      inference('sup+', [status(thm)], ['70', '71'])).
% 0.78/1.00  thf('81', plain,
% 0.78/1.00      (![X1 : $i, X2 : $i]:
% 0.78/1.00         ((k4_xboole_0 @ X1 @ X2)
% 0.78/1.00           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.78/1.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/1.00  thf('82', plain,
% 0.78/1.00      (![X0 : $i]:
% 0.78/1.00         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.78/1.00      inference('sup+', [status(thm)], ['80', '81'])).
% 0.78/1.00  thf('83', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.78/1.00      inference('demod', [status(thm)], ['74', '75'])).
% 0.78/1.00  thf('84', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/1.00      inference('demod', [status(thm)], ['82', '83'])).
% 0.78/1.00  thf('85', plain,
% 0.78/1.00      ((((k1_xboole_0) = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('demod', [status(thm)], ['62', '79', '84'])).
% 0.78/1.00  thf(t98_xboole_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.78/1.00  thf('86', plain,
% 0.78/1.00      (![X11 : $i, X12 : $i]:
% 0.78/1.00         ((k2_xboole_0 @ X11 @ X12)
% 0.78/1.00           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.78/1.00      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.78/1.00  thf('87', plain,
% 0.78/1.00      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.78/1.00          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['85', '86'])).
% 0.78/1.00  thf('88', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.78/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.78/1.00  thf('89', plain,
% 0.78/1.00      (![X1 : $i, X2 : $i]:
% 0.78/1.00         ((k4_xboole_0 @ X1 @ X2)
% 0.78/1.00           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.78/1.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/1.00  thf('90', plain,
% 0.78/1.00      (![X0 : $i]:
% 0.78/1.00         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.78/1.00      inference('sup+', [status(thm)], ['88', '89'])).
% 0.78/1.00  thf(t2_boole, axiom,
% 0.78/1.00    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.78/1.00  thf('91', plain,
% 0.78/1.00      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/1.00      inference('cnf', [status(esa)], [t2_boole])).
% 0.78/1.00  thf('92', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/1.00      inference('demod', [status(thm)], ['90', '91'])).
% 0.78/1.00  thf('93', plain,
% 0.78/1.00      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('demod', [status(thm)], ['87', '92'])).
% 0.78/1.00  thf('94', plain,
% 0.78/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf(dt_k2_tops_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( ( l1_pre_topc @ A ) & 
% 0.78/1.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.78/1.00       ( m1_subset_1 @
% 0.78/1.00         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.78/1.00  thf('95', plain,
% 0.78/1.00      (![X34 : $i, X35 : $i]:
% 0.78/1.00         (~ (l1_pre_topc @ X34)
% 0.78/1.00          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.78/1.00          | (m1_subset_1 @ (k2_tops_1 @ X34 @ X35) @ 
% 0.78/1.00             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 0.78/1.00      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.78/1.00  thf('96', plain,
% 0.78/1.00      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.78/1.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.78/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.78/1.00      inference('sup-', [status(thm)], ['94', '95'])).
% 0.78/1.00  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf('98', plain,
% 0.78/1.00      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.78/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/1.00      inference('demod', [status(thm)], ['96', '97'])).
% 0.78/1.00  thf('99', plain,
% 0.78/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf(redefinition_k4_subset_1, axiom,
% 0.78/1.00    (![A:$i,B:$i,C:$i]:
% 0.78/1.00     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.78/1.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/1.00       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.78/1.00  thf('100', plain,
% 0.78/1.00      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.78/1.00         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.78/1.00          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.78/1.00          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.78/1.00      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.78/1.00  thf('101', plain,
% 0.78/1.00      (![X0 : $i]:
% 0.78/1.00         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.78/1.00            = (k2_xboole_0 @ sk_B @ X0))
% 0.78/1.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['99', '100'])).
% 0.78/1.00  thf('102', plain,
% 0.78/1.00      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.78/1.00         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.78/1.00      inference('sup-', [status(thm)], ['98', '101'])).
% 0.78/1.00  thf('103', plain,
% 0.78/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf(t65_tops_1, axiom,
% 0.78/1.00    (![A:$i]:
% 0.78/1.00     ( ( l1_pre_topc @ A ) =>
% 0.78/1.00       ( ![B:$i]:
% 0.78/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/1.00           ( ( k2_pre_topc @ A @ B ) =
% 0.78/1.00             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.78/1.00  thf('104', plain,
% 0.78/1.00      (![X40 : $i, X41 : $i]:
% 0.78/1.00         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.78/1.00          | ((k2_pre_topc @ X41 @ X40)
% 0.78/1.00              = (k4_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 0.78/1.00                 (k2_tops_1 @ X41 @ X40)))
% 0.78/1.00          | ~ (l1_pre_topc @ X41))),
% 0.78/1.00      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.78/1.00  thf('105', plain,
% 0.78/1.00      ((~ (l1_pre_topc @ sk_A)
% 0.78/1.00        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.78/1.00            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['103', '104'])).
% 0.78/1.00  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf('107', plain,
% 0.78/1.00      (((k2_pre_topc @ sk_A @ sk_B)
% 0.78/1.00         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.78/1.00      inference('demod', [status(thm)], ['105', '106'])).
% 0.78/1.00  thf('108', plain,
% 0.78/1.00      (((k2_pre_topc @ sk_A @ sk_B)
% 0.78/1.00         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.78/1.00      inference('sup+', [status(thm)], ['102', '107'])).
% 0.78/1.00  thf('109', plain,
% 0.78/1.00      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['93', '108'])).
% 0.78/1.00  thf('110', plain,
% 0.78/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf(fc1_tops_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.78/1.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.78/1.00       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.78/1.00  thf('111', plain,
% 0.78/1.00      (![X36 : $i, X37 : $i]:
% 0.78/1.00         (~ (l1_pre_topc @ X36)
% 0.78/1.00          | ~ (v2_pre_topc @ X36)
% 0.78/1.00          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.78/1.00          | (v4_pre_topc @ (k2_pre_topc @ X36 @ X37) @ X36))),
% 0.78/1.00      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.78/1.00  thf('112', plain,
% 0.78/1.00      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.78/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.78/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.78/1.00      inference('sup-', [status(thm)], ['110', '111'])).
% 0.78/1.00  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf('115', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.78/1.00      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.78/1.00  thf('116', plain,
% 0.78/1.00      (((v4_pre_topc @ sk_B @ sk_A))
% 0.78/1.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.78/1.00      inference('sup+', [status(thm)], ['109', '115'])).
% 0.78/1.00  thf('117', plain,
% 0.78/1.00      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.78/1.00      inference('split', [status(esa)], ['0'])).
% 0.78/1.00  thf('118', plain,
% 0.78/1.00      (~
% 0.78/1.00       (((k2_tops_1 @ sk_A @ sk_B)
% 0.78/1.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.78/1.00             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.78/1.00       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.78/1.00      inference('sup-', [status(thm)], ['116', '117'])).
% 0.78/1.00  thf('119', plain, ($false),
% 0.78/1.00      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '118'])).
% 0.78/1.00  
% 0.78/1.00  % SZS output end Refutation
% 0.78/1.00  
% 0.78/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
