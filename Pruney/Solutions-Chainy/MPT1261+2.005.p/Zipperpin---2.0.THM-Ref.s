%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iqGmBdgzMW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:37 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 301 expanded)
%              Number of leaves         :   39 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          : 1310 (3193 expanded)
%              Number of equality atoms :  116 ( 252 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ X41 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','58'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k4_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','74'])).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','74'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','81','84'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('87',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('89',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('91',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_pre_topc @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
       != X35 )
      | ( v4_pre_topc @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iqGmBdgzMW
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.83/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.03  % Solved by: fo/fo7.sh
% 0.83/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.03  % done 1349 iterations in 0.577s
% 0.83/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.03  % SZS output start Refutation
% 0.83/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.83/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.83/1.03  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.83/1.03  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.83/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.03  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.83/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.83/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.03  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.83/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.03  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.83/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.83/1.03  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.83/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.03  thf(t77_tops_1, conjecture,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03           ( ( v4_pre_topc @ B @ A ) <=>
% 0.83/1.03             ( ( k2_tops_1 @ A @ B ) =
% 0.83/1.03               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.83/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.03    (~( ![A:$i]:
% 0.83/1.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03          ( ![B:$i]:
% 0.83/1.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03              ( ( v4_pre_topc @ B @ A ) <=>
% 0.83/1.03                ( ( k2_tops_1 @ A @ B ) =
% 0.83/1.03                  ( k7_subset_1 @
% 0.83/1.03                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.83/1.03    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.83/1.03  thf('0', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03              (k1_tops_1 @ sk_A @ sk_B)))
% 0.83/1.03        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('1', plain,
% 0.83/1.03      (~
% 0.83/1.03       (((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.83/1.03       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('split', [status(esa)], ['0'])).
% 0.83/1.03  thf('2', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03             (k1_tops_1 @ sk_A @ sk_B)))
% 0.83/1.03        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('3', plain,
% 0.83/1.03      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.83/1.03      inference('split', [status(esa)], ['2'])).
% 0.83/1.03  thf('4', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(t52_pre_topc, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( l1_pre_topc @ A ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.83/1.03             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.83/1.03               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.83/1.03  thf('5', plain,
% 0.83/1.03      (![X35 : $i, X36 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.83/1.03          | ~ (v4_pre_topc @ X35 @ X36)
% 0.83/1.03          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 0.83/1.03          | ~ (l1_pre_topc @ X36))),
% 0.83/1.03      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.83/1.03  thf('6', plain,
% 0.83/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.83/1.03        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('8', plain,
% 0.83/1.03      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('demod', [status(thm)], ['6', '7'])).
% 0.83/1.03  thf('9', plain,
% 0.83/1.03      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.83/1.03         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['3', '8'])).
% 0.83/1.03  thf('10', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(l78_tops_1, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( l1_pre_topc @ A ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03           ( ( k2_tops_1 @ A @ B ) =
% 0.83/1.03             ( k7_subset_1 @
% 0.83/1.03               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.83/1.03               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.83/1.03  thf('11', plain,
% 0.83/1.03      (![X39 : $i, X40 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.83/1.03          | ((k2_tops_1 @ X40 @ X39)
% 0.83/1.03              = (k7_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.83/1.03                 (k2_pre_topc @ X40 @ X39) @ (k1_tops_1 @ X40 @ X39)))
% 0.83/1.03          | ~ (l1_pre_topc @ X40))),
% 0.83/1.03      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.83/1.03  thf('12', plain,
% 0.83/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.03               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.03  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('14', plain,
% 0.83/1.03      (((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.83/1.03            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['12', '13'])).
% 0.83/1.03  thf('15', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03             (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.83/1.03      inference('sup+', [status(thm)], ['9', '14'])).
% 0.83/1.03  thf('16', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(redefinition_k7_subset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.03       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.83/1.03  thf('17', plain,
% 0.83/1.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.83/1.03          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.83/1.03  thf('18', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.83/1.03           = (k4_xboole_0 @ sk_B @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.03  thf('19', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.83/1.03      inference('demod', [status(thm)], ['15', '18'])).
% 0.83/1.03  thf('20', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.83/1.03           = (k4_xboole_0 @ sk_B @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.03  thf('21', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03              (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= (~
% 0.83/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('split', [status(esa)], ['0'])).
% 0.83/1.03  thf('22', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= (~
% 0.83/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.83/1.03  thf('23', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.83/1.03         <= (~
% 0.83/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.83/1.03             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['19', '22'])).
% 0.83/1.03  thf('24', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.83/1.03       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('simplify', [status(thm)], ['23'])).
% 0.83/1.03  thf('25', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.83/1.03       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('split', [status(esa)], ['2'])).
% 0.83/1.03  thf('26', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(dt_k2_tops_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.83/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.83/1.03       ( m1_subset_1 @
% 0.83/1.03         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/1.03  thf('27', plain,
% 0.83/1.03      (![X37 : $i, X38 : $i]:
% 0.83/1.03         (~ (l1_pre_topc @ X37)
% 0.83/1.03          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.83/1.03          | (m1_subset_1 @ (k2_tops_1 @ X37 @ X38) @ 
% 0.83/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 0.83/1.03      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.83/1.03  thf('28', plain,
% 0.83/1.03      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.83/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.03      inference('sup-', [status(thm)], ['26', '27'])).
% 0.83/1.03  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('30', plain,
% 0.83/1.03      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.83/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.03  thf('31', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(redefinition_k4_subset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.83/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.83/1.03       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.83/1.03  thf('32', plain,
% 0.83/1.03      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.83/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.83/1.03          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.83/1.03  thf('33', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.83/1.03            = (k2_xboole_0 @ sk_B @ X0))
% 0.83/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['31', '32'])).
% 0.83/1.03  thf('34', plain,
% 0.83/1.03      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.83/1.03         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['30', '33'])).
% 0.83/1.03  thf('35', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(t65_tops_1, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( l1_pre_topc @ A ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03           ( ( k2_pre_topc @ A @ B ) =
% 0.83/1.03             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.83/1.03  thf('36', plain,
% 0.83/1.03      (![X41 : $i, X42 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.83/1.03          | ((k2_pre_topc @ X42 @ X41)
% 0.83/1.03              = (k4_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 0.83/1.03                 (k2_tops_1 @ X42 @ X41)))
% 0.83/1.03          | ~ (l1_pre_topc @ X42))),
% 0.83/1.03      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.83/1.03  thf('37', plain,
% 0.83/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.83/1.03            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['35', '36'])).
% 0.83/1.03  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('39', plain,
% 0.83/1.03      (((k2_pre_topc @ sk_A @ sk_B)
% 0.83/1.03         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['37', '38'])).
% 0.83/1.03  thf('40', plain,
% 0.83/1.03      (((k2_pre_topc @ sk_A @ sk_B)
% 0.83/1.03         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('sup+', [status(thm)], ['34', '39'])).
% 0.83/1.03  thf('41', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.83/1.03           = (k4_xboole_0 @ sk_B @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.03  thf('42', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03             (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('split', [status(esa)], ['2'])).
% 0.83/1.03  thf('43', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['41', '42'])).
% 0.83/1.03  thf(t48_xboole_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.83/1.03  thf('44', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.83/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.83/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.03  thf('45', plain,
% 0.83/1.03      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.83/1.03          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['43', '44'])).
% 0.83/1.03  thf('46', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.83/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.83/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.03  thf('47', plain,
% 0.83/1.03      ((((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.83/1.03          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['45', '46'])).
% 0.83/1.03  thf(t47_xboole_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.83/1.03  thf('48', plain,
% 0.83/1.03      (![X15 : $i, X16 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.83/1.03           = (k4_xboole_0 @ X15 @ X16))),
% 0.83/1.03      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.83/1.03  thf('49', plain,
% 0.83/1.03      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.03          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('demod', [status(thm)], ['47', '48'])).
% 0.83/1.03  thf('50', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['41', '42'])).
% 0.83/1.03  thf('51', plain,
% 0.83/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['49', '50'])).
% 0.83/1.03  thf(commutativity_k2_tarski, axiom,
% 0.83/1.03    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.83/1.03  thf('52', plain,
% 0.83/1.03      (![X21 : $i, X22 : $i]:
% 0.83/1.03         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.83/1.03      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.83/1.03  thf(t12_setfam_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.83/1.03  thf('53', plain,
% 0.83/1.03      (![X31 : $i, X32 : $i]:
% 0.83/1.03         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.83/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.83/1.03  thf('54', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.03      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.03  thf('55', plain,
% 0.83/1.03      (![X31 : $i, X32 : $i]:
% 0.83/1.03         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.83/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.83/1.03  thf('56', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.03      inference('sup+', [status(thm)], ['54', '55'])).
% 0.83/1.03  thf('57', plain,
% 0.83/1.03      (![X15 : $i, X16 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.83/1.03           = (k4_xboole_0 @ X15 @ X16))),
% 0.83/1.03      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.83/1.03  thf('58', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.83/1.03           = (k4_xboole_0 @ X0 @ X1))),
% 0.83/1.03      inference('sup+', [status(thm)], ['56', '57'])).
% 0.83/1.03  thf('59', plain,
% 0.83/1.03      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.83/1.03          = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['51', '58'])).
% 0.83/1.03  thf(t3_boole, axiom,
% 0.83/1.03    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.03  thf('60', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.03  thf('61', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.83/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.83/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.03  thf('62', plain,
% 0.83/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['60', '61'])).
% 0.83/1.03  thf('63', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.03      inference('sup+', [status(thm)], ['54', '55'])).
% 0.83/1.03  thf('64', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.83/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.83/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.03  thf(d10_xboole_0, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.03  thf('65', plain,
% 0.83/1.03      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.83/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.03  thf('66', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.83/1.03      inference('simplify', [status(thm)], ['65'])).
% 0.83/1.03  thf(t109_xboole_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.83/1.03  thf('67', plain,
% 0.83/1.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/1.03         (~ (r1_tarski @ X9 @ X10)
% 0.83/1.03          | (r1_tarski @ (k4_xboole_0 @ X9 @ X11) @ X10))),
% 0.83/1.03      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.83/1.03  thf('68', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.83/1.03      inference('sup-', [status(thm)], ['66', '67'])).
% 0.83/1.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.83/1.03  thf('69', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.83/1.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.83/1.03  thf('70', plain,
% 0.83/1.03      (![X4 : $i, X6 : $i]:
% 0.83/1.03         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.83/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.03  thf('71', plain,
% 0.83/1.03      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['69', '70'])).
% 0.83/1.03  thf('72', plain,
% 0.83/1.03      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['68', '71'])).
% 0.83/1.03  thf('73', plain,
% 0.83/1.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['64', '72'])).
% 0.83/1.03  thf('74', plain,
% 0.83/1.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['63', '73'])).
% 0.83/1.03  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.03      inference('demod', [status(thm)], ['62', '74'])).
% 0.83/1.03  thf('76', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.83/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.83/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.03  thf('77', plain,
% 0.83/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['75', '76'])).
% 0.83/1.03  thf('78', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.03  thf('79', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.83/1.03      inference('demod', [status(thm)], ['77', '78'])).
% 0.83/1.03  thf(t100_xboole_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.83/1.03  thf('80', plain,
% 0.83/1.03      (![X7 : $i, X8 : $i]:
% 0.83/1.03         ((k4_xboole_0 @ X7 @ X8)
% 0.83/1.03           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.83/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.83/1.03  thf('81', plain,
% 0.83/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['79', '80'])).
% 0.83/1.03  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.03      inference('demod', [status(thm)], ['62', '74'])).
% 0.83/1.03  thf('83', plain,
% 0.83/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['79', '80'])).
% 0.83/1.03  thf('84', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.03      inference('demod', [status(thm)], ['82', '83'])).
% 0.83/1.03  thf('85', plain,
% 0.83/1.03      ((((k1_xboole_0) = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('demod', [status(thm)], ['59', '81', '84'])).
% 0.83/1.03  thf(t98_xboole_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.83/1.03  thf('86', plain,
% 0.83/1.03      (![X19 : $i, X20 : $i]:
% 0.83/1.03         ((k2_xboole_0 @ X19 @ X20)
% 0.83/1.03           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.83/1.03      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.83/1.03  thf('87', plain,
% 0.83/1.03      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.83/1.03          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['85', '86'])).
% 0.83/1.03  thf('88', plain,
% 0.83/1.03      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['68', '71'])).
% 0.83/1.03  thf('89', plain,
% 0.83/1.03      (![X19 : $i, X20 : $i]:
% 0.83/1.03         ((k2_xboole_0 @ X19 @ X20)
% 0.83/1.03           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.83/1.03      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.83/1.03  thf('90', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['88', '89'])).
% 0.83/1.03  thf(t1_boole, axiom,
% 0.83/1.03    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.03  thf('91', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.83/1.03      inference('cnf', [status(esa)], [t1_boole])).
% 0.83/1.03  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.83/1.03      inference('sup+', [status(thm)], ['90', '91'])).
% 0.83/1.03  thf('93', plain,
% 0.83/1.03      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('demod', [status(thm)], ['87', '92'])).
% 0.83/1.03  thf('94', plain,
% 0.83/1.03      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup+', [status(thm)], ['40', '93'])).
% 0.83/1.03  thf('95', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('96', plain,
% 0.83/1.03      (![X35 : $i, X36 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.83/1.03          | ~ (v2_pre_topc @ X36)
% 0.83/1.03          | ((k2_pre_topc @ X36 @ X35) != (X35))
% 0.83/1.03          | (v4_pre_topc @ X35 @ X36)
% 0.83/1.03          | ~ (l1_pre_topc @ X36))),
% 0.83/1.03      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.83/1.03  thf('97', plain,
% 0.83/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | (v4_pre_topc @ sk_B @ sk_A)
% 0.83/1.03        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.83/1.03        | ~ (v2_pre_topc @ sk_A))),
% 0.83/1.03      inference('sup-', [status(thm)], ['95', '96'])).
% 0.83/1.03  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('100', plain,
% 0.83/1.03      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.83/1.03  thf('101', plain,
% 0.83/1.03      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['94', '100'])).
% 0.83/1.03  thf('102', plain,
% 0.83/1.03      (((v4_pre_topc @ sk_B @ sk_A))
% 0.83/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.83/1.03      inference('simplify', [status(thm)], ['101'])).
% 0.83/1.03  thf('103', plain,
% 0.83/1.03      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.83/1.03      inference('split', [status(esa)], ['0'])).
% 0.83/1.03  thf('104', plain,
% 0.83/1.03      (~
% 0.83/1.03       (((k2_tops_1 @ sk_A @ sk_B)
% 0.83/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.83/1.03             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.83/1.03       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.83/1.03      inference('sup-', [status(thm)], ['102', '103'])).
% 0.83/1.03  thf('105', plain, ($false),
% 0.83/1.03      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '104'])).
% 0.83/1.03  
% 0.83/1.03  % SZS output end Refutation
% 0.83/1.03  
% 0.83/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
