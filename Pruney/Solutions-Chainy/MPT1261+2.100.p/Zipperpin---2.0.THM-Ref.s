%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f0HaXYerIG

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:53 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 427 expanded)
%              Number of leaves         :   40 ( 140 expanded)
%              Depth                    :   23
%              Number of atoms          : 1767 (4725 expanded)
%              Number of equality atoms :  148 ( 336 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v4_pre_topc @ X34 @ X35 )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_tops_1 @ X41 @ X40 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k2_pre_topc @ X41 @ X40 ) @ ( k1_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_pre_topc @ X43 @ X42 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X43 ) @ X42 @ ( k2_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('64',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','68','69'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('73',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['75','81'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('83',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('87',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['76'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('94',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('95',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['82','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['74','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('108',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('113',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('114',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['111','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','119'])).

thf('121',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('122',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','124'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('126',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('127',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('129',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','132'])).

thf('134',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('136',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X38 @ X39 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('137',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['134','140'])).

thf('142',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('143',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f0HaXYerIG
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:44:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.42/1.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.42/1.66  % Solved by: fo/fo7.sh
% 1.42/1.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.42/1.66  % done 3901 iterations in 1.187s
% 1.42/1.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.42/1.66  % SZS output start Refutation
% 1.42/1.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.42/1.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.42/1.66  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.42/1.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.42/1.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.42/1.66  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.42/1.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.42/1.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.42/1.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.42/1.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.42/1.66  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.42/1.66  thf(sk_A_type, type, sk_A: $i).
% 1.42/1.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.42/1.66  thf(sk_B_type, type, sk_B: $i).
% 1.42/1.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.42/1.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.42/1.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.42/1.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.42/1.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.42/1.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.42/1.66  thf(t77_tops_1, conjecture,
% 1.42/1.66    (![A:$i]:
% 1.42/1.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.42/1.66       ( ![B:$i]:
% 1.42/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.66           ( ( v4_pre_topc @ B @ A ) <=>
% 1.42/1.66             ( ( k2_tops_1 @ A @ B ) =
% 1.42/1.66               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.42/1.66  thf(zf_stmt_0, negated_conjecture,
% 1.42/1.66    (~( ![A:$i]:
% 1.42/1.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.42/1.66          ( ![B:$i]:
% 1.42/1.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.66              ( ( v4_pre_topc @ B @ A ) <=>
% 1.42/1.66                ( ( k2_tops_1 @ A @ B ) =
% 1.42/1.66                  ( k7_subset_1 @
% 1.42/1.66                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.42/1.66    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.42/1.66  thf('0', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66              (k1_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('1', plain,
% 1.42/1.66      (~
% 1.42/1.66       (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.42/1.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('split', [status(esa)], ['0'])).
% 1.42/1.66  thf('2', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66             (k1_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('3', plain,
% 1.42/1.66      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.66      inference('split', [status(esa)], ['2'])).
% 1.42/1.66  thf('4', plain,
% 1.42/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf(t52_pre_topc, axiom,
% 1.42/1.66    (![A:$i]:
% 1.42/1.66     ( ( l1_pre_topc @ A ) =>
% 1.42/1.66       ( ![B:$i]:
% 1.42/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.66           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.42/1.66             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.42/1.66               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.42/1.66  thf('5', plain,
% 1.42/1.66      (![X34 : $i, X35 : $i]:
% 1.42/1.66         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.42/1.66          | ~ (v4_pre_topc @ X34 @ X35)
% 1.42/1.66          | ((k2_pre_topc @ X35 @ X34) = (X34))
% 1.42/1.66          | ~ (l1_pre_topc @ X35))),
% 1.42/1.66      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.42/1.66  thf('6', plain,
% 1.42/1.66      ((~ (l1_pre_topc @ sk_A)
% 1.42/1.66        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.42/1.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('sup-', [status(thm)], ['4', '5'])).
% 1.42/1.66  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('8', plain,
% 1.42/1.66      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('demod', [status(thm)], ['6', '7'])).
% 1.42/1.66  thf('9', plain,
% 1.42/1.66      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.42/1.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.66      inference('sup-', [status(thm)], ['3', '8'])).
% 1.42/1.66  thf('10', plain,
% 1.42/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf(l78_tops_1, axiom,
% 1.42/1.66    (![A:$i]:
% 1.42/1.66     ( ( l1_pre_topc @ A ) =>
% 1.42/1.66       ( ![B:$i]:
% 1.42/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.66           ( ( k2_tops_1 @ A @ B ) =
% 1.42/1.66             ( k7_subset_1 @
% 1.42/1.66               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.42/1.66               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.42/1.66  thf('11', plain,
% 1.42/1.66      (![X40 : $i, X41 : $i]:
% 1.42/1.66         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.42/1.66          | ((k2_tops_1 @ X41 @ X40)
% 1.42/1.66              = (k7_subset_1 @ (u1_struct_0 @ X41) @ 
% 1.42/1.66                 (k2_pre_topc @ X41 @ X40) @ (k1_tops_1 @ X41 @ X40)))
% 1.42/1.66          | ~ (l1_pre_topc @ X41))),
% 1.42/1.66      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.42/1.66  thf('12', plain,
% 1.42/1.66      ((~ (l1_pre_topc @ sk_A)
% 1.42/1.66        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.42/1.66               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['10', '11'])).
% 1.42/1.66  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('14', plain,
% 1.42/1.66      (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.42/1.66            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.66      inference('demod', [status(thm)], ['12', '13'])).
% 1.42/1.66  thf('15', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66             (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['9', '14'])).
% 1.42/1.66  thf('16', plain,
% 1.42/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf(redefinition_k7_subset_1, axiom,
% 1.42/1.66    (![A:$i,B:$i,C:$i]:
% 1.42/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.42/1.66       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.42/1.66  thf('17', plain,
% 1.42/1.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.42/1.66         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 1.42/1.66          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 1.42/1.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.42/1.66  thf('18', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.66           = (k4_xboole_0 @ sk_B @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['16', '17'])).
% 1.42/1.66  thf('19', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.66      inference('demod', [status(thm)], ['15', '18'])).
% 1.42/1.66  thf('20', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.66           = (k4_xboole_0 @ sk_B @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['16', '17'])).
% 1.42/1.66  thf('21', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66              (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= (~
% 1.42/1.66             (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('split', [status(esa)], ['0'])).
% 1.42/1.66  thf('22', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= (~
% 1.42/1.66             (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['20', '21'])).
% 1.42/1.66  thf('23', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66         <= (~
% 1.42/1.66             (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.42/1.66             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.66      inference('sup-', [status(thm)], ['19', '22'])).
% 1.42/1.66  thf('24', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.42/1.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('simplify', [status(thm)], ['23'])).
% 1.42/1.66  thf('25', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.42/1.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('split', [status(esa)], ['2'])).
% 1.42/1.66  thf('26', plain,
% 1.42/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf(dt_k2_tops_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( ( l1_pre_topc @ A ) & 
% 1.42/1.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.42/1.66       ( m1_subset_1 @
% 1.42/1.66         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.42/1.66  thf('27', plain,
% 1.42/1.66      (![X36 : $i, X37 : $i]:
% 1.42/1.66         (~ (l1_pre_topc @ X36)
% 1.42/1.66          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.42/1.66          | (m1_subset_1 @ (k2_tops_1 @ X36 @ X37) @ 
% 1.42/1.66             (k1_zfmisc_1 @ (u1_struct_0 @ X36))))),
% 1.42/1.66      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.42/1.66  thf('28', plain,
% 1.42/1.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.42/1.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.42/1.66        | ~ (l1_pre_topc @ sk_A))),
% 1.42/1.66      inference('sup-', [status(thm)], ['26', '27'])).
% 1.42/1.66  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('30', plain,
% 1.42/1.66      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.42/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('demod', [status(thm)], ['28', '29'])).
% 1.42/1.66  thf('31', plain,
% 1.42/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf(redefinition_k4_subset_1, axiom,
% 1.42/1.66    (![A:$i,B:$i,C:$i]:
% 1.42/1.66     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.42/1.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.42/1.66       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.42/1.66  thf('32', plain,
% 1.42/1.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.42/1.66         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 1.42/1.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 1.42/1.66          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 1.42/1.66      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.42/1.66  thf('33', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.66            = (k2_xboole_0 @ sk_B @ X0))
% 1.42/1.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['31', '32'])).
% 1.42/1.66  thf('34', plain,
% 1.42/1.66      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.66         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.66      inference('sup-', [status(thm)], ['30', '33'])).
% 1.42/1.66  thf('35', plain,
% 1.42/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf(t65_tops_1, axiom,
% 1.42/1.66    (![A:$i]:
% 1.42/1.66     ( ( l1_pre_topc @ A ) =>
% 1.42/1.66       ( ![B:$i]:
% 1.42/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.66           ( ( k2_pre_topc @ A @ B ) =
% 1.42/1.66             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.42/1.66  thf('36', plain,
% 1.42/1.66      (![X42 : $i, X43 : $i]:
% 1.42/1.66         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.42/1.66          | ((k2_pre_topc @ X43 @ X42)
% 1.42/1.66              = (k4_subset_1 @ (u1_struct_0 @ X43) @ X42 @ 
% 1.42/1.66                 (k2_tops_1 @ X43 @ X42)))
% 1.42/1.66          | ~ (l1_pre_topc @ X43))),
% 1.42/1.66      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.42/1.66  thf('37', plain,
% 1.42/1.66      ((~ (l1_pre_topc @ sk_A)
% 1.42/1.66        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.42/1.66            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['35', '36'])).
% 1.42/1.66  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('39', plain,
% 1.42/1.66      (((k2_pre_topc @ sk_A @ sk_B)
% 1.42/1.66         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.66      inference('demod', [status(thm)], ['37', '38'])).
% 1.42/1.66  thf('40', plain,
% 1.42/1.66      (((k2_pre_topc @ sk_A @ sk_B)
% 1.42/1.66         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['34', '39'])).
% 1.42/1.66  thf('41', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.66           = (k4_xboole_0 @ sk_B @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['16', '17'])).
% 1.42/1.66  thf('42', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66             (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('split', [status(esa)], ['2'])).
% 1.42/1.66  thf('43', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['41', '42'])).
% 1.42/1.66  thf(t36_xboole_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.42/1.66  thf('44', plain,
% 1.42/1.66      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.42/1.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.42/1.66  thf(t3_subset, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.42/1.66  thf('45', plain,
% 1.42/1.66      (![X28 : $i, X30 : $i]:
% 1.42/1.66         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 1.42/1.66      inference('cnf', [status(esa)], [t3_subset])).
% 1.42/1.66  thf('46', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['44', '45'])).
% 1.42/1.66  thf('47', plain,
% 1.42/1.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['43', '46'])).
% 1.42/1.66  thf(d5_subset_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.42/1.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.42/1.66  thf('48', plain,
% 1.42/1.66      (![X17 : $i, X18 : $i]:
% 1.42/1.66         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 1.42/1.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.42/1.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.66  thf('49', plain,
% 1.42/1.66      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['47', '48'])).
% 1.42/1.66  thf('50', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['41', '42'])).
% 1.42/1.66  thf(t48_xboole_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.42/1.66  thf('51', plain,
% 1.42/1.66      (![X13 : $i, X14 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.42/1.66           = (k3_xboole_0 @ X13 @ X14))),
% 1.42/1.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.66  thf('52', plain,
% 1.42/1.66      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.66          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['50', '51'])).
% 1.42/1.66  thf('53', plain,
% 1.42/1.66      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.66          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['49', '52'])).
% 1.42/1.66  thf('54', plain,
% 1.42/1.66      (![X13 : $i, X14 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.42/1.66           = (k3_xboole_0 @ X13 @ X14))),
% 1.42/1.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.66  thf('55', plain,
% 1.42/1.66      (![X13 : $i, X14 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.42/1.66           = (k3_xboole_0 @ X13 @ X14))),
% 1.42/1.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.66  thf('56', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.42/1.66           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['54', '55'])).
% 1.42/1.66  thf('57', plain,
% 1.42/1.66      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66          = (k3_xboole_0 @ sk_B @ 
% 1.42/1.66             (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['53', '56'])).
% 1.42/1.66  thf('58', plain,
% 1.42/1.66      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['47', '48'])).
% 1.42/1.66  thf('59', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['44', '45'])).
% 1.42/1.66  thf('60', plain,
% 1.42/1.66      (![X17 : $i, X18 : $i]:
% 1.42/1.66         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 1.42/1.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.42/1.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.66  thf('61', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.42/1.66           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.42/1.66      inference('sup-', [status(thm)], ['59', '60'])).
% 1.42/1.66  thf('62', plain,
% 1.42/1.66      ((((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ 
% 1.42/1.66             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['58', '61'])).
% 1.42/1.66  thf('63', plain,
% 1.42/1.66      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['47', '48'])).
% 1.42/1.66  thf('64', plain,
% 1.42/1.66      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ 
% 1.42/1.66             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('demod', [status(thm)], ['62', '63'])).
% 1.42/1.66  thf('65', plain,
% 1.42/1.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['43', '46'])).
% 1.42/1.66  thf(involutiveness_k3_subset_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.42/1.66       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.42/1.66  thf('66', plain,
% 1.42/1.66      (![X19 : $i, X20 : $i]:
% 1.42/1.66         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 1.42/1.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.42/1.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.42/1.66  thf('67', plain,
% 1.42/1.66      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup-', [status(thm)], ['65', '66'])).
% 1.42/1.66  thf('68', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ 
% 1.42/1.66             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('demod', [status(thm)], ['64', '67'])).
% 1.42/1.66  thf('69', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['41', '42'])).
% 1.42/1.66  thf('70', plain,
% 1.42/1.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('demod', [status(thm)], ['57', '68', '69'])).
% 1.42/1.66  thf(commutativity_k2_xboole_0, axiom,
% 1.42/1.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.42/1.66  thf('71', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.42/1.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.42/1.66  thf('72', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.42/1.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.42/1.66  thf(t1_boole, axiom,
% 1.42/1.66    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.42/1.66  thf('73', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.42/1.66      inference('cnf', [status(esa)], [t1_boole])).
% 1.42/1.66  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.42/1.66      inference('sup+', [status(thm)], ['72', '73'])).
% 1.42/1.66  thf(t41_xboole_1, axiom,
% 1.42/1.66    (![A:$i,B:$i,C:$i]:
% 1.42/1.66     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.42/1.66       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.42/1.66  thf('75', plain,
% 1.42/1.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.42/1.66           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.42/1.66      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.42/1.66  thf(d10_xboole_0, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.42/1.66  thf('76', plain,
% 1.42/1.66      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.42/1.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.42/1.66  thf('77', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.42/1.66      inference('simplify', [status(thm)], ['76'])).
% 1.42/1.66  thf('78', plain,
% 1.42/1.66      (![X28 : $i, X30 : $i]:
% 1.42/1.66         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 1.42/1.66      inference('cnf', [status(esa)], [t3_subset])).
% 1.42/1.66  thf('79', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['77', '78'])).
% 1.42/1.66  thf('80', plain,
% 1.42/1.66      (![X17 : $i, X18 : $i]:
% 1.42/1.66         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 1.42/1.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.42/1.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.66  thf('81', plain,
% 1.42/1.66      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['79', '80'])).
% 1.42/1.66  thf('82', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.42/1.66           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['75', '81'])).
% 1.42/1.66  thf(t4_subset_1, axiom,
% 1.42/1.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.42/1.66  thf('83', plain,
% 1.42/1.66      (![X27 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 1.42/1.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.42/1.66  thf('84', plain,
% 1.42/1.66      (![X19 : $i, X20 : $i]:
% 1.42/1.66         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 1.42/1.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.42/1.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.42/1.66  thf('85', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['83', '84'])).
% 1.42/1.66  thf('86', plain,
% 1.42/1.66      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['79', '80'])).
% 1.42/1.66  thf('87', plain,
% 1.42/1.66      (![X13 : $i, X14 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.42/1.66           = (k3_xboole_0 @ X13 @ X14))),
% 1.42/1.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.66  thf('88', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0))
% 1.42/1.66           = (k3_xboole_0 @ X0 @ X0))),
% 1.42/1.66      inference('sup+', [status(thm)], ['86', '87'])).
% 1.42/1.66  thf('89', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.42/1.66      inference('simplify', [status(thm)], ['76'])).
% 1.42/1.66  thf(t28_xboole_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.42/1.66  thf('90', plain,
% 1.42/1.66      (![X6 : $i, X7 : $i]:
% 1.42/1.66         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.42/1.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.42/1.66  thf('91', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['89', '90'])).
% 1.42/1.66  thf('92', plain,
% 1.42/1.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.42/1.66      inference('demod', [status(thm)], ['88', '91'])).
% 1.42/1.66  thf('93', plain,
% 1.42/1.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.42/1.66           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.42/1.66      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.42/1.66  thf('94', plain,
% 1.42/1.66      (![X27 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 1.42/1.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.42/1.66  thf('95', plain,
% 1.42/1.66      (![X17 : $i, X18 : $i]:
% 1.42/1.66         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 1.42/1.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.42/1.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.66  thf('96', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['94', '95'])).
% 1.42/1.66  thf('97', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 1.42/1.66           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['93', '96'])).
% 1.42/1.66  thf('98', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.42/1.66      inference('cnf', [status(esa)], [t1_boole])).
% 1.42/1.66  thf('99', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 1.42/1.66           = (k4_xboole_0 @ X1 @ X0))),
% 1.42/1.66      inference('demod', [status(thm)], ['97', '98'])).
% 1.42/1.66  thf('100', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k3_subset_1 @ X0 @ k1_xboole_0)
% 1.42/1.66           = (k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['92', '99'])).
% 1.42/1.66  thf('101', plain,
% 1.42/1.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.42/1.66      inference('demod', [status(thm)], ['88', '91'])).
% 1.42/1.66  thf('102', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.42/1.66      inference('demod', [status(thm)], ['100', '101'])).
% 1.42/1.66  thf('103', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.42/1.66      inference('demod', [status(thm)], ['85', '102'])).
% 1.42/1.66  thf('104', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k1_xboole_0)
% 1.42/1.66           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.42/1.66      inference('demod', [status(thm)], ['82', '103'])).
% 1.42/1.66  thf('105', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['74', '104'])).
% 1.42/1.66  thf('106', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['94', '95'])).
% 1.42/1.66  thf('107', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.42/1.66      inference('demod', [status(thm)], ['100', '101'])).
% 1.42/1.66  thf('108', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.42/1.66      inference('demod', [status(thm)], ['106', '107'])).
% 1.42/1.66  thf('109', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.42/1.66      inference('demod', [status(thm)], ['105', '108'])).
% 1.42/1.66  thf('110', plain,
% 1.42/1.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.42/1.66           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.42/1.66      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.42/1.66  thf('111', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.42/1.66           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['109', '110'])).
% 1.42/1.66  thf('112', plain,
% 1.42/1.66      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.42/1.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.42/1.66  thf('113', plain,
% 1.42/1.66      (![X27 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 1.42/1.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.42/1.66  thf('114', plain,
% 1.42/1.66      (![X28 : $i, X29 : $i]:
% 1.42/1.66         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 1.42/1.66      inference('cnf', [status(esa)], [t3_subset])).
% 1.42/1.66  thf('115', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.42/1.66      inference('sup-', [status(thm)], ['113', '114'])).
% 1.42/1.66  thf('116', plain,
% 1.42/1.66      (![X2 : $i, X4 : $i]:
% 1.42/1.66         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.42/1.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.42/1.66  thf('117', plain,
% 1.42/1.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.42/1.66      inference('sup-', [status(thm)], ['115', '116'])).
% 1.42/1.66  thf('118', plain,
% 1.42/1.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['112', '117'])).
% 1.42/1.66  thf('119', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.42/1.66      inference('demod', [status(thm)], ['111', '118'])).
% 1.42/1.66  thf('120', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['71', '119'])).
% 1.42/1.66  thf('121', plain,
% 1.42/1.66      (![X13 : $i, X14 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.42/1.66           = (k3_xboole_0 @ X13 @ X14))),
% 1.42/1.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.66  thf('122', plain,
% 1.42/1.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.42/1.66           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.42/1.66      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.42/1.66  thf('123', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.42/1.66           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.42/1.66      inference('sup+', [status(thm)], ['121', '122'])).
% 1.42/1.66  thf('124', plain,
% 1.42/1.66      (![X0 : $i, X1 : $i]:
% 1.42/1.66         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.42/1.66      inference('sup+', [status(thm)], ['120', '123'])).
% 1.42/1.66  thf('125', plain,
% 1.42/1.66      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['70', '124'])).
% 1.42/1.66  thf(t98_xboole_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.42/1.66  thf('126', plain,
% 1.42/1.66      (![X15 : $i, X16 : $i]:
% 1.42/1.66         ((k2_xboole_0 @ X15 @ X16)
% 1.42/1.66           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 1.42/1.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.42/1.66  thf('127', plain,
% 1.42/1.66      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.66          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['125', '126'])).
% 1.42/1.66  thf('128', plain,
% 1.42/1.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.42/1.66      inference('sup-', [status(thm)], ['112', '117'])).
% 1.42/1.66  thf('129', plain,
% 1.42/1.66      (![X15 : $i, X16 : $i]:
% 1.42/1.66         ((k2_xboole_0 @ X15 @ X16)
% 1.42/1.66           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 1.42/1.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.42/1.66  thf('130', plain,
% 1.42/1.66      (![X0 : $i]:
% 1.42/1.66         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.42/1.66      inference('sup+', [status(thm)], ['128', '129'])).
% 1.42/1.66  thf('131', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.42/1.66      inference('cnf', [status(esa)], [t1_boole])).
% 1.42/1.66  thf('132', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.42/1.66      inference('sup+', [status(thm)], ['130', '131'])).
% 1.42/1.66  thf('133', plain,
% 1.42/1.66      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('demod', [status(thm)], ['127', '132'])).
% 1.42/1.66  thf('134', plain,
% 1.42/1.66      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['40', '133'])).
% 1.42/1.66  thf('135', plain,
% 1.42/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf(fc1_tops_1, axiom,
% 1.42/1.66    (![A:$i,B:$i]:
% 1.42/1.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.42/1.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.42/1.66       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.42/1.66  thf('136', plain,
% 1.42/1.66      (![X38 : $i, X39 : $i]:
% 1.42/1.66         (~ (l1_pre_topc @ X38)
% 1.42/1.66          | ~ (v2_pre_topc @ X38)
% 1.42/1.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.42/1.66          | (v4_pre_topc @ (k2_pre_topc @ X38 @ X39) @ X38))),
% 1.42/1.66      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.42/1.66  thf('137', plain,
% 1.42/1.66      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.42/1.66        | ~ (v2_pre_topc @ sk_A)
% 1.42/1.66        | ~ (l1_pre_topc @ sk_A))),
% 1.42/1.66      inference('sup-', [status(thm)], ['135', '136'])).
% 1.42/1.66  thf('138', plain, ((v2_pre_topc @ sk_A)),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.66  thf('140', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.42/1.66      inference('demod', [status(thm)], ['137', '138', '139'])).
% 1.42/1.66  thf('141', plain,
% 1.42/1.66      (((v4_pre_topc @ sk_B @ sk_A))
% 1.42/1.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.66      inference('sup+', [status(thm)], ['134', '140'])).
% 1.42/1.66  thf('142', plain,
% 1.42/1.66      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.66      inference('split', [status(esa)], ['0'])).
% 1.42/1.66  thf('143', plain,
% 1.42/1.66      (~
% 1.42/1.66       (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.42/1.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.66      inference('sup-', [status(thm)], ['141', '142'])).
% 1.42/1.66  thf('144', plain, ($false),
% 1.42/1.66      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '143'])).
% 1.42/1.66  
% 1.42/1.66  % SZS output end Refutation
% 1.42/1.66  
% 1.42/1.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
