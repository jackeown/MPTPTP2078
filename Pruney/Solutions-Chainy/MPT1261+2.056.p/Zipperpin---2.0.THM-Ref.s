%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YZH0YQT2i0

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:46 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 244 expanded)
%              Number of leaves         :   39 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          : 1182 (3134 expanded)
%              Number of equality atoms :   83 ( 176 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( v4_pre_topc @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['61','74'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('78',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('79',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('82',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X33 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('83',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['80','86'])).

thf('88',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YZH0YQT2i0
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:08:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 2470 iterations in 0.818s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.06/1.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.28  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.06/1.28  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.06/1.28  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.06/1.28  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.06/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.06/1.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.28  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.28  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.06/1.28  thf(t77_tops_1, conjecture,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28           ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.28             ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.28               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i]:
% 1.06/1.28        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28          ( ![B:$i]:
% 1.06/1.28            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28              ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.28                ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.28                  ( k7_subset_1 @
% 1.06/1.28                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.06/1.28  thf('0', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28              (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('1', plain,
% 1.06/1.28      (~
% 1.06/1.28       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.28       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28             (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('3', plain,
% 1.06/1.28      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('split', [status(esa)], ['2'])).
% 1.06/1.28  thf('4', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t69_tops_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( l1_pre_topc @ A ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28           ( ( v4_pre_topc @ B @ A ) =>
% 1.06/1.28             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.06/1.28  thf('5', plain,
% 1.06/1.28      (![X37 : $i, X38 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.06/1.28          | (r1_tarski @ (k2_tops_1 @ X38 @ X37) @ X37)
% 1.06/1.28          | ~ (v4_pre_topc @ X37 @ X38)
% 1.06/1.28          | ~ (l1_pre_topc @ X38))),
% 1.06/1.28      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.28        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.06/1.28        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.28  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.06/1.28        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['6', '7'])).
% 1.06/1.28  thf('9', plain,
% 1.06/1.28      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.06/1.28         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['3', '8'])).
% 1.06/1.28  thf(t3_subset, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      (![X28 : $i, X30 : $i]:
% 1.06/1.28         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.28  thf('11', plain,
% 1.06/1.28      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.28         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.28  thf(involutiveness_k3_subset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.28       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.06/1.28  thf('12', plain,
% 1.06/1.28      (![X18 : $i, X19 : $i]:
% 1.06/1.28         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 1.06/1.28          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.06/1.28      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.28  thf('13', plain,
% 1.06/1.28      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['11', '12'])).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t74_tops_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( l1_pre_topc @ A ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28           ( ( k1_tops_1 @ A @ B ) =
% 1.06/1.28             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.28  thf('15', plain,
% 1.06/1.28      (![X39 : $i, X40 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.06/1.28          | ((k1_tops_1 @ X40 @ X39)
% 1.06/1.28              = (k7_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 1.06/1.28                 (k2_tops_1 @ X40 @ X39)))
% 1.06/1.28          | ~ (l1_pre_topc @ X40))),
% 1.06/1.28      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.06/1.28  thf('16', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.28        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.28            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['14', '15'])).
% 1.06/1.28  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('18', plain,
% 1.06/1.28      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['16', '17'])).
% 1.06/1.28  thf('19', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(redefinition_k7_subset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.28       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.06/1.28  thf('20', plain,
% 1.06/1.28      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.06/1.28          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.06/1.28  thf('21', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.28           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.28  thf('22', plain,
% 1.06/1.28      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '21'])).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.28         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.28  thf(d5_subset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.28       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.06/1.28  thf('24', plain,
% 1.06/1.28      (![X16 : $i, X17 : $i]:
% 1.06/1.28         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 1.06/1.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.28  thf('25', plain,
% 1.06/1.28      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.28          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['23', '24'])).
% 1.06/1.28  thf('26', plain,
% 1.06/1.28      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.28          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['22', '25'])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.28          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('demod', [status(thm)], ['13', '26'])).
% 1.06/1.28  thf('28', plain,
% 1.06/1.28      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '21'])).
% 1.06/1.28  thf(t36_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.06/1.28  thf('29', plain,
% 1.06/1.28      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.06/1.28      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X28 : $i, X30 : $i]:
% 1.06/1.28         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.28  thf('32', plain,
% 1.06/1.28      (![X16 : $i, X17 : $i]:
% 1.06/1.28         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 1.06/1.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.06/1.28           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['31', '32'])).
% 1.06/1.28  thf('34', plain,
% 1.06/1.28      (((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['28', '33'])).
% 1.06/1.28  thf('35', plain,
% 1.06/1.28      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '21'])).
% 1.06/1.28  thf('36', plain,
% 1.06/1.28      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.28         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['34', '35'])).
% 1.06/1.28  thf('37', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.28           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.28  thf('38', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28              (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('39', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.28  thf('40', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['36', '39'])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.06/1.28             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['27', '40'])).
% 1.06/1.28  thf('42', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.28       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.28      inference('simplify', [status(thm)], ['41'])).
% 1.06/1.28  thf('43', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.28       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.28      inference('split', [status(esa)], ['2'])).
% 1.06/1.28  thf('44', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(dt_k2_tops_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( l1_pre_topc @ A ) & 
% 1.06/1.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.28       ( m1_subset_1 @
% 1.06/1.28         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.28  thf('45', plain,
% 1.06/1.28      (![X31 : $i, X32 : $i]:
% 1.06/1.28         (~ (l1_pre_topc @ X31)
% 1.06/1.28          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.06/1.28          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 1.06/1.28             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.06/1.28  thf('46', plain,
% 1.06/1.28      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['44', '45'])).
% 1.06/1.28  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('48', plain,
% 1.06/1.28      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('demod', [status(thm)], ['46', '47'])).
% 1.06/1.28  thf('49', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(redefinition_k4_subset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.06/1.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.06/1.28       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.28  thf('50', plain,
% 1.06/1.28      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.06/1.28          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 1.06/1.28          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.06/1.28  thf('51', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.28            = (k2_xboole_0 @ sk_B @ X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['49', '50'])).
% 1.06/1.28  thf('52', plain,
% 1.06/1.28      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.28         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['48', '51'])).
% 1.06/1.28  thf('53', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t65_tops_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( l1_pre_topc @ A ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28           ( ( k2_pre_topc @ A @ B ) =
% 1.06/1.28             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.28  thf('54', plain,
% 1.06/1.28      (![X35 : $i, X36 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.06/1.28          | ((k2_pre_topc @ X36 @ X35)
% 1.06/1.28              = (k4_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 1.06/1.28                 (k2_tops_1 @ X36 @ X35)))
% 1.06/1.28          | ~ (l1_pre_topc @ X36))),
% 1.06/1.28      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.06/1.28  thf('55', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.28        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.28            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['53', '54'])).
% 1.06/1.28  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('57', plain,
% 1.06/1.28      (((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.28         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['55', '56'])).
% 1.06/1.28  thf('58', plain,
% 1.06/1.28      (((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.28         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['52', '57'])).
% 1.06/1.28  thf('59', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.28           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.28  thf('60', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28             (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('split', [status(esa)], ['2'])).
% 1.06/1.28  thf('61', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup+', [status(thm)], ['59', '60'])).
% 1.06/1.28  thf('62', plain,
% 1.06/1.28      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.06/1.28      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.28  thf(l32_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.28  thf('63', plain,
% 1.06/1.28      (![X0 : $i, X2 : $i]:
% 1.06/1.28         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.28  thf('64', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['62', '63'])).
% 1.06/1.28  thf(t51_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.06/1.28       ( A ) ))).
% 1.06/1.28  thf('65', plain,
% 1.06/1.28      (![X10 : $i, X11 : $i]:
% 1.06/1.28         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 1.06/1.28           = (X10))),
% 1.06/1.28      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.06/1.28  thf('66', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ 
% 1.06/1.28           k1_xboole_0) = (k4_xboole_0 @ X1 @ X0))),
% 1.06/1.28      inference('sup+', [status(thm)], ['64', '65'])).
% 1.06/1.28  thf(t1_boole, axiom,
% 1.06/1.28    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.28  thf('67', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.06/1.28      inference('cnf', [status(esa)], [t1_boole])).
% 1.06/1.28  thf('68', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.06/1.28           = (k4_xboole_0 @ X1 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['66', '67'])).
% 1.06/1.28  thf(commutativity_k2_tarski, axiom,
% 1.06/1.28    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.06/1.28  thf('69', plain,
% 1.06/1.28      (![X12 : $i, X13 : $i]:
% 1.06/1.28         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 1.06/1.28      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.28  thf(t12_setfam_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.28  thf('70', plain,
% 1.06/1.28      (![X26 : $i, X27 : $i]:
% 1.06/1.28         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 1.06/1.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.28  thf('71', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['69', '70'])).
% 1.06/1.28  thf('72', plain,
% 1.06/1.28      (![X26 : $i, X27 : $i]:
% 1.06/1.28         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 1.06/1.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.28  thf('73', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['71', '72'])).
% 1.06/1.28  thf('74', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.06/1.28           = (k4_xboole_0 @ X1 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['68', '73'])).
% 1.06/1.28  thf('75', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.28          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup+', [status(thm)], ['61', '74'])).
% 1.06/1.28  thf('76', plain,
% 1.06/1.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup+', [status(thm)], ['59', '60'])).
% 1.06/1.28  thf('77', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.28          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('demod', [status(thm)], ['75', '76'])).
% 1.06/1.28  thf(t22_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.06/1.28  thf('78', plain,
% 1.06/1.28      (![X6 : $i, X7 : $i]:
% 1.06/1.28         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 1.06/1.28      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.06/1.28  thf('79', plain,
% 1.06/1.28      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup+', [status(thm)], ['77', '78'])).
% 1.06/1.28  thf('80', plain,
% 1.06/1.28      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup+', [status(thm)], ['58', '79'])).
% 1.06/1.28  thf('81', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(fc1_tops_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.06/1.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.28       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.06/1.28  thf('82', plain,
% 1.06/1.28      (![X33 : $i, X34 : $i]:
% 1.06/1.28         (~ (l1_pre_topc @ X33)
% 1.06/1.28          | ~ (v2_pre_topc @ X33)
% 1.06/1.28          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.06/1.28          | (v4_pre_topc @ (k2_pre_topc @ X33 @ X34) @ X33))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.06/1.28  thf('83', plain,
% 1.06/1.28      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['81', '82'])).
% 1.06/1.28  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('86', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.28      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.06/1.28  thf('87', plain,
% 1.06/1.28      (((v4_pre_topc @ sk_B @ sk_A))
% 1.06/1.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.28      inference('sup+', [status(thm)], ['80', '86'])).
% 1.06/1.28  thf('88', plain,
% 1.06/1.28      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('89', plain,
% 1.06/1.28      (~
% 1.06/1.28       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.28             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.28       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['87', '88'])).
% 1.06/1.28  thf('90', plain, ($false),
% 1.06/1.28      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '89'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
