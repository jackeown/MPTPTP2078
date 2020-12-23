%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sr1CWPn8h

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:03 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 170 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  983 (2368 expanded)
%              Number of equality atoms :   69 ( 137 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_tops_1 @ X23 @ X22 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k2_pre_topc @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('45',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( k2_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','58'])).

thf('60',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('63',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','66'])).

thf('68',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sr1CWPn8h
% 0.14/0.37  % Computer   : n010.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:51:59 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 139 iterations in 0.102s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.42/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.42/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.42/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(t77_tops_1, conjecture,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.42/0.59             ( ( k2_tops_1 @ A @ B ) =
% 0.42/0.59               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i]:
% 0.42/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59              ( ( v4_pre_topc @ B @ A ) <=>
% 0.42/0.59                ( ( k2_tops_1 @ A @ B ) =
% 0.42/0.59                  ( k7_subset_1 @
% 0.42/0.59                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.42/0.59  thf('0', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59              (k1_tops_1 @ sk_A @ sk_B)))
% 0.42/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      (~
% 0.42/0.59       (((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.42/0.59       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('split', [status(esa)], ['0'])).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59             (k1_tops_1 @ sk_A @ sk_B)))
% 0.42/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.42/0.59      inference('split', [status(esa)], ['2'])).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t52_pre_topc, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.42/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.42/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X16 : $i, X17 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.42/0.59          | ~ (v4_pre_topc @ X16 @ X17)
% 0.42/0.59          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.42/0.59          | ~ (l1_pre_topc @ X17))),
% 0.42/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.42/0.59  thf('6', plain,
% 0.42/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.59        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.42/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.59  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.42/0.59  thf('9', plain,
% 0.42/0.59      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.42/0.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['3', '8'])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(l78_tops_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( k2_tops_1 @ A @ B ) =
% 0.42/0.59             ( k7_subset_1 @
% 0.42/0.59               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.42/0.59               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      (![X22 : $i, X23 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.59          | ((k2_tops_1 @ X23 @ X22)
% 0.42/0.59              = (k7_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.42/0.59                 (k2_pre_topc @ X23 @ X22) @ (k1_tops_1 @ X23 @ X22)))
% 0.42/0.59          | ~ (l1_pre_topc @ X23))),
% 0.42/0.59      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.59        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.59               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.59  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      (((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.42/0.59            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59             (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.42/0.59      inference('sup+', [status(thm)], ['9', '14'])).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(redefinition_k7_subset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.42/0.59          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.42/0.59           = (k4_xboole_0 @ sk_B @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('19', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.42/0.59      inference('demod', [status(thm)], ['15', '18'])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.42/0.59           = (k4_xboole_0 @ sk_B @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59              (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= (~
% 0.42/0.59             (((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('split', [status(esa)], ['0'])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= (~
% 0.42/0.59             (((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.42/0.59         <= (~
% 0.42/0.59             (((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.42/0.59             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['19', '22'])).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.42/0.59       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.42/0.59       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('split', [status(esa)], ['2'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t74_tops_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( k1_tops_1 @ A @ B ) =
% 0.42/0.59             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      (![X26 : $i, X27 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.42/0.59          | ((k1_tops_1 @ X27 @ X26)
% 0.42/0.59              = (k7_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.42/0.59                 (k2_tops_1 @ X27 @ X26)))
% 0.42/0.59          | ~ (l1_pre_topc @ X27))),
% 0.42/0.59      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.59        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.42/0.59            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.59  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.42/0.59           = (k4_xboole_0 @ sk_B @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      (((k1_tops_1 @ sk_A @ sk_B)
% 0.42/0.59         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.42/0.59           = (k4_xboole_0 @ sk_B @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59             (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('split', [status(esa)], ['2'])).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf(t48_xboole_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      (![X4 : $i, X5 : $i]:
% 0.42/0.59         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.42/0.59           = (k3_xboole_0 @ X4 @ X5))),
% 0.42/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.42/0.59          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['31', '36'])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      (![X4 : $i, X5 : $i]:
% 0.42/0.59         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.42/0.59           = (k3_xboole_0 @ X4 @ X5))),
% 0.42/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      (![X4 : $i, X5 : $i]:
% 0.42/0.59         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.42/0.59           = (k3_xboole_0 @ X4 @ X5))),
% 0.42/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.59  thf('40', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.42/0.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.42/0.59      inference('sup+', [status(thm)], ['38', '39'])).
% 0.42/0.59  thf(t22_xboole_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.42/0.59  thf('41', plain,
% 0.42/0.59      (![X2 : $i, X3 : $i]:
% 0.42/0.59         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.42/0.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.42/0.59           = (X1))),
% 0.42/0.59      inference('sup+', [status(thm)], ['40', '41'])).
% 0.42/0.59  thf('43', plain,
% 0.42/0.59      ((((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.42/0.59          = (sk_B)))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['37', '42'])).
% 0.42/0.59  thf('44', plain,
% 0.42/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf('45', plain,
% 0.42/0.59      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.59  thf('46', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t65_tops_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( k2_pre_topc @ A @ B ) =
% 0.42/0.59             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.59  thf('47', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.42/0.59          | ((k2_pre_topc @ X25 @ X24)
% 0.42/0.59              = (k4_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 0.42/0.59                 (k2_tops_1 @ X25 @ X24)))
% 0.42/0.59          | ~ (l1_pre_topc @ X25))),
% 0.42/0.59      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.42/0.59  thf('48', plain,
% 0.42/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.59        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.42/0.59            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.42/0.59  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('50', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(dt_k2_tops_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( l1_pre_topc @ A ) & 
% 0.42/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.59       ( m1_subset_1 @
% 0.42/0.59         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.42/0.59  thf('51', plain,
% 0.42/0.59      (![X18 : $i, X19 : $i]:
% 0.42/0.59         (~ (l1_pre_topc @ X18)
% 0.42/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.59          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 0.42/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.42/0.59      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.42/0.59  thf('52', plain,
% 0.42/0.59      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.42/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.59  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('54', plain,
% 0.42/0.59      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.42/0.59  thf('55', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(redefinition_k4_subset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.42/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.42/0.59  thf('56', plain,
% 0.42/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.42/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 0.42/0.59          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.42/0.59  thf('57', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.42/0.59            = (k2_xboole_0 @ sk_B @ X0))
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.59  thf('58', plain,
% 0.42/0.59      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.42/0.59         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['54', '57'])).
% 0.42/0.59  thf('59', plain,
% 0.42/0.59      (((k2_pre_topc @ sk_A @ sk_B)
% 0.42/0.59         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('demod', [status(thm)], ['48', '49', '58'])).
% 0.42/0.59  thf('60', plain,
% 0.42/0.59      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['45', '59'])).
% 0.42/0.59  thf('61', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(fc1_tops_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.42/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.59       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.42/0.59  thf('62', plain,
% 0.42/0.59      (![X20 : $i, X21 : $i]:
% 0.42/0.59         (~ (l1_pre_topc @ X20)
% 0.42/0.59          | ~ (v2_pre_topc @ X20)
% 0.42/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.42/0.59          | (v4_pre_topc @ (k2_pre_topc @ X20 @ X21) @ X20))),
% 0.42/0.59      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.42/0.59  thf('63', plain,
% 0.42/0.59      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.42/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.42/0.59  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('66', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.42/0.59      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.42/0.59  thf('67', plain,
% 0.42/0.59      (((v4_pre_topc @ sk_B @ sk_A))
% 0.42/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['60', '66'])).
% 0.42/0.59  thf('68', plain,
% 0.42/0.59      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.42/0.59      inference('split', [status(esa)], ['0'])).
% 0.42/0.59  thf('69', plain,
% 0.42/0.59      (~
% 0.42/0.59       (((k2_tops_1 @ sk_A @ sk_B)
% 0.42/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.42/0.59       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.59  thf('70', plain, ($false),
% 0.42/0.59      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '69'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
