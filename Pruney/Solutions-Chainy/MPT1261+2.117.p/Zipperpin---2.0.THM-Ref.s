%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZwmdIIoBo0

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:55 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 403 expanded)
%              Number of leaves         :   38 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          : 1697 (5118 expanded)
%              Number of equality atoms :  123 ( 323 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
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

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('34',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X1 ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('69',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('82',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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

thf('96',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','80','95'])).

thf('97',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','96'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('100',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('101',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('102',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['98','105'])).

thf('107',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf('108',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['97','108'])).

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
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X30 @ X31 ) @ X30 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZwmdIIoBo0
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.60/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.84  % Solved by: fo/fo7.sh
% 0.60/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.84  % done 952 iterations in 0.380s
% 0.60/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.84  % SZS output start Refutation
% 0.60/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.84  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.60/0.84  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.60/0.84  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.60/0.84  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.60/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.84  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.60/0.84  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.60/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.84  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.60/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.60/0.84  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.60/0.84  thf(t77_tops_1, conjecture,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.84           ( ( v4_pre_topc @ B @ A ) <=>
% 0.60/0.84             ( ( k2_tops_1 @ A @ B ) =
% 0.60/0.84               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.84    (~( ![A:$i]:
% 0.60/0.84        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.84          ( ![B:$i]:
% 0.60/0.84            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.84              ( ( v4_pre_topc @ B @ A ) <=>
% 0.60/0.84                ( ( k2_tops_1 @ A @ B ) =
% 0.60/0.84                  ( k7_subset_1 @
% 0.60/0.84                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.60/0.84    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.60/0.84  thf('0', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84              (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.84        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('1', plain,
% 0.60/0.84      (~
% 0.60/0.84       (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.60/0.84       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.84      inference('split', [status(esa)], ['0'])).
% 0.60/0.84  thf('2', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84             (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.84        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('3', plain,
% 0.60/0.84      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.84      inference('split', [status(esa)], ['2'])).
% 0.60/0.84  thf('4', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t52_pre_topc, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( l1_pre_topc @ A ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.84           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.60/0.84             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.60/0.84               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.60/0.84  thf('5', plain,
% 0.60/0.84      (![X26 : $i, X27 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.60/0.84          | ~ (v4_pre_topc @ X26 @ X27)
% 0.60/0.84          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 0.60/0.84          | ~ (l1_pre_topc @ X27))),
% 0.60/0.84      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.60/0.84  thf('6', plain,
% 0.60/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.84        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.60/0.84        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.84  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('8', plain,
% 0.60/0.84      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['6', '7'])).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.60/0.84         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['3', '8'])).
% 0.60/0.84  thf('10', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(l78_tops_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( l1_pre_topc @ A ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.84           ( ( k2_tops_1 @ A @ B ) =
% 0.60/0.84             ( k7_subset_1 @
% 0.60/0.84               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.60/0.84               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.84  thf('11', plain,
% 0.60/0.84      (![X32 : $i, X33 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.60/0.84          | ((k2_tops_1 @ X33 @ X32)
% 0.60/0.84              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 0.60/0.84                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 0.60/0.84          | ~ (l1_pre_topc @ X33))),
% 0.60/0.84      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.60/0.84  thf('12', plain,
% 0.60/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.84        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.84               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.60/0.84            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.60/0.84      inference('demod', [status(thm)], ['12', '13'])).
% 0.60/0.84  thf('15', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84             (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['9', '14'])).
% 0.60/0.84  thf('16', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k7_subset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.84       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.60/0.84          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.60/0.84  thf('18', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.84           = (k4_xboole_0 @ sk_B @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['15', '18'])).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.84           = (k4_xboole_0 @ sk_B @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84              (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= (~
% 0.60/0.84             (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('split', [status(esa)], ['0'])).
% 0.60/0.84  thf('22', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= (~
% 0.60/0.84             (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.84  thf('23', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.84         <= (~
% 0.60/0.84             (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.60/0.84             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['19', '22'])).
% 0.60/0.84  thf('24', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.60/0.84       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.84      inference('simplify', [status(thm)], ['23'])).
% 0.60/0.84  thf('25', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.60/0.84       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.84      inference('split', [status(esa)], ['2'])).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.84           = (k4_xboole_0 @ sk_B @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84             (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('split', [status(esa)], ['2'])).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('sup+', [status(thm)], ['26', '27'])).
% 0.60/0.84  thf(t36_xboole_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.60/0.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.60/0.84  thf(t3_subset, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      (![X23 : $i, X25 : $i]:
% 0.60/0.84         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.60/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.60/0.84         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('sup+', [status(thm)], ['28', '31'])).
% 0.60/0.84  thf(involutiveness_k3_subset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.84       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (![X13 : $i, X14 : $i]:
% 0.60/0.84         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.60/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.60/0.84      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.84          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.84         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['32', '33'])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('sup+', [status(thm)], ['26', '27'])).
% 0.60/0.84  thf('36', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.84  thf(d5_subset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.84       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      (![X11 : $i, X12 : $i]:
% 0.60/0.84         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.60/0.84          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.60/0.84      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.60/0.84           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.84  thf(t48_xboole_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      (![X8 : $i, X9 : $i]:
% 0.60/0.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.84           = (k3_xboole_0 @ X8 @ X9))),
% 0.60/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.84           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['38', '39'])).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.84          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.84         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.84                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.84      inference('sup+', [status(thm)], ['35', '40'])).
% 0.60/0.84  thf('42', plain,
% 0.60/0.84      ((((k3_subset_1 @ sk_B @ (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.84          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.84         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.84                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['34', '41'])).
% 0.60/0.85  thf('43', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.85           = (k3_xboole_0 @ X8 @ X9))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('44', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.85           = (k3_xboole_0 @ X8 @ X9))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('45', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.60/0.85           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['43', '44'])).
% 0.60/0.85  thf(t100_xboole_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.60/0.85  thf('46', plain,
% 0.60/0.85      (![X2 : $i, X3 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X2 @ X3)
% 0.60/0.85           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.85  thf('47', plain,
% 0.60/0.85      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.60/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.60/0.85  thf('48', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (r1_tarski @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 0.60/0.85      inference('sup+', [status(thm)], ['46', '47'])).
% 0.60/0.85  thf('49', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (r1_tarski @ 
% 0.60/0.85          (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.60/0.85          X1)),
% 0.60/0.85      inference('sup+', [status(thm)], ['45', '48'])).
% 0.60/0.85  thf('50', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.85           = (k3_xboole_0 @ X8 @ X9))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('51', plain,
% 0.60/0.85      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.60/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.60/0.85  thf('52', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.60/0.85      inference('sup+', [status(thm)], ['50', '51'])).
% 0.60/0.85  thf('53', plain,
% 0.60/0.85      (![X23 : $i, X25 : $i]:
% 0.60/0.85         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.60/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.85  thf('54', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['52', '53'])).
% 0.60/0.85  thf('55', plain,
% 0.60/0.85      (![X11 : $i, X12 : $i]:
% 0.60/0.85         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.60/0.85          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.60/0.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.60/0.85  thf('56', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.60/0.85           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['54', '55'])).
% 0.60/0.85  thf('57', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (r1_tarski @ 
% 0.60/0.85          (k5_xboole_0 @ X1 @ (k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.60/0.85          X1)),
% 0.60/0.85      inference('demod', [status(thm)], ['49', '56'])).
% 0.60/0.85  thf('58', plain,
% 0.60/0.85      (![X23 : $i, X25 : $i]:
% 0.60/0.85         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.60/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.85  thf('59', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (m1_subset_1 @ 
% 0.60/0.85          (k5_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))) @ 
% 0.60/0.85          (k1_zfmisc_1 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['57', '58'])).
% 0.60/0.85  thf('60', plain,
% 0.60/0.85      (((m1_subset_1 @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.60/0.85         (k1_zfmisc_1 @ sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['42', '59'])).
% 0.60/0.85  thf('61', plain,
% 0.60/0.85      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['28', '31'])).
% 0.60/0.85  thf(redefinition_k4_subset_1, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i]:
% 0.60/0.85     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.60/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.60/0.85       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.60/0.85  thf('62', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.60/0.85          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.60/0.85          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.60/0.85  thf('63', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.60/0.85             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.60/0.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['61', '62'])).
% 0.60/0.85  thf('64', plain,
% 0.60/0.85      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85          (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85             (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['60', '63'])).
% 0.60/0.85  thf('65', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['26', '27'])).
% 0.60/0.85  thf('66', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.85           = (k3_xboole_0 @ X8 @ X9))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('67', plain,
% 0.60/0.85      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['65', '66'])).
% 0.60/0.85  thf(t39_xboole_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.85  thf('68', plain,
% 0.60/0.85      (![X6 : $i, X7 : $i]:
% 0.60/0.85         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.60/0.85           = (k2_xboole_0 @ X6 @ X7))),
% 0.60/0.85      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.85  thf('69', plain,
% 0.60/0.85      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['67', '68'])).
% 0.60/0.85  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.85    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.85  thf('70', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.85      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.85  thf('71', plain,
% 0.60/0.85      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['69', '70'])).
% 0.60/0.85  thf('72', plain,
% 0.60/0.85      ((((k3_subset_1 @ sk_B @ (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['34', '41'])).
% 0.60/0.85  thf('73', plain,
% 0.60/0.85      (![X2 : $i, X3 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X2 @ X3)
% 0.60/0.85           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.85  thf('74', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.85           = (k3_xboole_0 @ X8 @ X9))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('75', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.60/0.85           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.85      inference('sup+', [status(thm)], ['73', '74'])).
% 0.60/0.85  thf('76', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.85           = (k3_xboole_0 @ X8 @ X9))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('77', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.85           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.85      inference('sup+', [status(thm)], ['38', '39'])).
% 0.60/0.85  thf('78', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.60/0.85           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['76', '77'])).
% 0.60/0.85  thf('79', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k5_xboole_0 @ X1 @ (k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.60/0.85           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.85      inference('demod', [status(thm)], ['75', '78'])).
% 0.60/0.85  thf('80', plain,
% 0.60/0.85      ((((k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['72', '79'])).
% 0.60/0.85  thf('81', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(dt_k2_tops_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( l1_pre_topc @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.85       ( m1_subset_1 @
% 0.60/0.85         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.85  thf('82', plain,
% 0.60/0.85      (![X28 : $i, X29 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ X28)
% 0.60/0.85          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.60/0.85          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 0.60/0.85             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.60/0.85  thf('83', plain,
% 0.60/0.85      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['81', '82'])).
% 0.60/0.85  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('85', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['83', '84'])).
% 0.60/0.85  thf('86', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('87', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.60/0.85          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.60/0.85          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.60/0.85  thf('88', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.85            = (k2_xboole_0 @ sk_B @ X0))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['86', '87'])).
% 0.60/0.85  thf('89', plain,
% 0.60/0.85      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['85', '88'])).
% 0.60/0.85  thf('90', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t65_tops_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_pre_topc @ A ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( k2_pre_topc @ A @ B ) =
% 0.60/0.85             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.85  thf('91', plain,
% 0.60/0.85      (![X34 : $i, X35 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.60/0.85          | ((k2_pre_topc @ X35 @ X34)
% 0.60/0.85              = (k4_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.60/0.85                 (k2_tops_1 @ X35 @ X34)))
% 0.60/0.85          | ~ (l1_pre_topc @ X35))),
% 0.60/0.85      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.60/0.85  thf('92', plain,
% 0.60/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.85        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.60/0.85            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['90', '91'])).
% 0.60/0.85  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('94', plain,
% 0.60/0.85      (((k2_pre_topc @ sk_A @ sk_B)
% 0.60/0.85         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['92', '93'])).
% 0.60/0.85  thf('95', plain,
% 0.60/0.85      (((k2_pre_topc @ sk_A @ sk_B)
% 0.60/0.85         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['89', '94'])).
% 0.60/0.85  thf('96', plain,
% 0.60/0.85      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85          (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['71', '80', '95'])).
% 0.60/0.85  thf('97', plain,
% 0.60/0.85      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85          (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['64', '96'])).
% 0.60/0.85  thf('98', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['26', '27'])).
% 0.60/0.85  thf('99', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.85  thf(t25_subset_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.85       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.60/0.85         ( k2_subset_1 @ A ) ) ))).
% 0.60/0.85  thf('100', plain,
% 0.60/0.85      (![X21 : $i, X22 : $i]:
% 0.60/0.85         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 0.60/0.85            = (k2_subset_1 @ X21))
% 0.60/0.85          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.60/0.85      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.60/0.85  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.60/0.85  thf('101', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.60/0.85  thf('102', plain,
% 0.60/0.85      (![X21 : $i, X22 : $i]:
% 0.60/0.85         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 0.60/0.85          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.60/0.85      inference('demod', [status(thm)], ['100', '101'])).
% 0.60/0.85  thf('103', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.60/0.85           (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))) = (X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['99', '102'])).
% 0.60/0.85  thf('104', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.85           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.85      inference('sup+', [status(thm)], ['38', '39'])).
% 0.60/0.85  thf('105', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.60/0.85           = (X0))),
% 0.60/0.85      inference('demod', [status(thm)], ['103', '104'])).
% 0.60/0.85  thf('106', plain,
% 0.60/0.85      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['98', '105'])).
% 0.60/0.85  thf('107', plain,
% 0.60/0.85      ((((k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['72', '79'])).
% 0.60/0.85  thf('108', plain,
% 0.60/0.85      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85          (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('109', plain,
% 0.60/0.85      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['97', '108'])).
% 0.60/0.85  thf('110', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(fc1_tops_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.85       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.60/0.85  thf('111', plain,
% 0.60/0.85      (![X30 : $i, X31 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ X30)
% 0.60/0.85          | ~ (v2_pre_topc @ X30)
% 0.60/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.60/0.85          | (v4_pre_topc @ (k2_pre_topc @ X30 @ X31) @ X30))),
% 0.60/0.85      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.60/0.85  thf('112', plain,
% 0.60/0.85      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.60/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['110', '111'])).
% 0.60/0.85  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('115', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.60/0.85  thf('116', plain,
% 0.60/0.85      (((v4_pre_topc @ sk_B @ sk_A))
% 0.60/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup+', [status(thm)], ['109', '115'])).
% 0.60/0.85  thf('117', plain,
% 0.60/0.85      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.85      inference('split', [status(esa)], ['0'])).
% 0.60/0.85  thf('118', plain,
% 0.60/0.85      (~
% 0.60/0.85       (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.60/0.85       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['116', '117'])).
% 0.60/0.85  thf('119', plain, ($false),
% 0.60/0.85      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '118'])).
% 0.60/0.85  
% 0.60/0.85  % SZS output end Refutation
% 0.60/0.85  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
