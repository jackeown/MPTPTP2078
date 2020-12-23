%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lu6VNxOjT5

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:03 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 218 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          : 1077 (2855 expanded)
%              Number of equality atoms :   74 ( 156 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( k2_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
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

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
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
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['61','68'])).

thf('70',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
       != X23 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lu6VNxOjT5
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.89/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.06  % Solved by: fo/fo7.sh
% 0.89/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.06  % done 1372 iterations in 0.602s
% 0.89/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.06  % SZS output start Refutation
% 0.89/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.06  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.89/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.06  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.89/1.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.89/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.06  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.89/1.06  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.89/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.06  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.89/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.06  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.89/1.06  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.89/1.06  thf(t77_tops_1, conjecture,
% 0.89/1.06    (![A:$i]:
% 0.89/1.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.06       ( ![B:$i]:
% 0.89/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.06           ( ( v4_pre_topc @ B @ A ) <=>
% 0.89/1.06             ( ( k2_tops_1 @ A @ B ) =
% 0.89/1.06               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.89/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.06    (~( ![A:$i]:
% 0.89/1.06        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.06          ( ![B:$i]:
% 0.89/1.06            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.06              ( ( v4_pre_topc @ B @ A ) <=>
% 0.89/1.06                ( ( k2_tops_1 @ A @ B ) =
% 0.89/1.06                  ( k7_subset_1 @
% 0.89/1.06                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.89/1.06    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.89/1.06  thf('0', plain,
% 0.89/1.06      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.06          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.06              (k1_tops_1 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('1', plain,
% 0.89/1.06      (~
% 0.89/1.06       (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.06          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.06             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.06       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.06      inference('split', [status(esa)], ['0'])).
% 0.89/1.06  thf('2', plain,
% 0.89/1.06      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.06          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.06             (k1_tops_1 @ sk_A @ sk_B)))
% 0.89/1.06        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('3', plain,
% 0.89/1.06      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.06      inference('split', [status(esa)], ['2'])).
% 0.89/1.06  thf('4', plain,
% 0.89/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf(t69_tops_1, axiom,
% 0.89/1.06    (![A:$i]:
% 0.89/1.06     ( ( l1_pre_topc @ A ) =>
% 0.89/1.06       ( ![B:$i]:
% 0.89/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.06           ( ( v4_pre_topc @ B @ A ) =>
% 0.89/1.06             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.89/1.06  thf('5', plain,
% 0.89/1.06      (![X29 : $i, X30 : $i]:
% 0.89/1.06         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.89/1.06          | (r1_tarski @ (k2_tops_1 @ X30 @ X29) @ X29)
% 0.89/1.06          | ~ (v4_pre_topc @ X29 @ X30)
% 0.89/1.06          | ~ (l1_pre_topc @ X30))),
% 0.89/1.06      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.89/1.06  thf('6', plain,
% 0.89/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.06        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.89/1.06        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.89/1.06      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.06  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('8', plain,
% 0.89/1.06      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.89/1.06        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.89/1.06      inference('demod', [status(thm)], ['6', '7'])).
% 0.89/1.06  thf('9', plain,
% 0.89/1.06      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.89/1.06         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['3', '8'])).
% 0.89/1.06  thf(t3_subset, axiom,
% 0.89/1.06    (![A:$i,B:$i]:
% 0.89/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.89/1.06  thf('10', plain,
% 0.89/1.06      (![X20 : $i, X22 : $i]:
% 0.89/1.06         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.89/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.89/1.06  thf('11', plain,
% 0.89/1.06      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.89/1.06         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.06  thf(involutiveness_k3_subset_1, axiom,
% 0.89/1.06    (![A:$i,B:$i]:
% 0.89/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.06       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.89/1.06  thf('12', plain,
% 0.89/1.06      (![X12 : $i, X13 : $i]:
% 0.89/1.06         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.89/1.06          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.89/1.06      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.89/1.06  thf('13', plain,
% 0.89/1.06      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.89/1.07  thf('14', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(t74_tops_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( l1_pre_topc @ A ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.07           ( ( k1_tops_1 @ A @ B ) =
% 0.89/1.07             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.07  thf('15', plain,
% 0.89/1.07      (![X31 : $i, X32 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.89/1.07          | ((k1_tops_1 @ X32 @ X31)
% 0.89/1.07              = (k7_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.89/1.07                 (k2_tops_1 @ X32 @ X31)))
% 0.89/1.07          | ~ (l1_pre_topc @ X32))),
% 0.89/1.07      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.89/1.07  thf('16', plain,
% 0.89/1.07      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.07        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.07            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['14', '15'])).
% 0.89/1.07  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('18', plain,
% 0.89/1.07      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.07         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['16', '17'])).
% 0.89/1.07  thf('19', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(redefinition_k7_subset_1, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i]:
% 0.89/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.07       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.89/1.07  thf('20', plain,
% 0.89/1.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.89/1.07          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.89/1.07  thf('21', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.07           = (k4_xboole_0 @ sk_B @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.07  thf('22', plain,
% 0.89/1.07      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.07         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['18', '21'])).
% 0.89/1.07  thf('23', plain,
% 0.89/1.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.89/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf(d5_subset_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.07       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.89/1.07  thf('24', plain,
% 0.89/1.07      (![X10 : $i, X11 : $i]:
% 0.89/1.07         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.89/1.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.89/1.07      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.89/1.07  thf('25', plain,
% 0.89/1.07      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.89/1.07          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.89/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.07  thf('26', plain,
% 0.89/1.07      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.89/1.07          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.89/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['22', '25'])).
% 0.89/1.07  thf('27', plain,
% 0.89/1.07      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.89/1.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.07      inference('demod', [status(thm)], ['13', '26'])).
% 0.89/1.07  thf('28', plain,
% 0.89/1.07      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.07         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['18', '21'])).
% 0.89/1.07  thf(t36_xboole_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.89/1.07  thf('29', plain,
% 0.89/1.07      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.89/1.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.89/1.07  thf('30', plain,
% 0.89/1.07      (![X20 : $i, X22 : $i]:
% 0.89/1.07         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.89/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.89/1.07  thf('31', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['29', '30'])).
% 0.89/1.07  thf('32', plain,
% 0.89/1.07      (![X10 : $i, X11 : $i]:
% 0.89/1.07         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.89/1.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.89/1.07      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.89/1.07  thf('33', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.89/1.07           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.07  thf('34', plain,
% 0.89/1.07      (((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.07         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['28', '33'])).
% 0.89/1.07  thf('35', plain,
% 0.89/1.07      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.07         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['18', '21'])).
% 0.89/1.07  thf('36', plain,
% 0.89/1.07      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.89/1.07         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.07  thf('37', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.07           = (k4_xboole_0 @ sk_B @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.07  thf('38', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07              (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.07         <= (~
% 0.89/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('split', [status(esa)], ['0'])).
% 0.89/1.07  thf('39', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.07         <= (~
% 0.89/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['37', '38'])).
% 0.89/1.07  thf('40', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.07         <= (~
% 0.89/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['36', '39'])).
% 0.89/1.07  thf('41', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.89/1.07             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['27', '40'])).
% 0.89/1.07  thf('42', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['41'])).
% 0.89/1.07  thf('43', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.07       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.07      inference('split', [status(esa)], ['2'])).
% 0.89/1.07  thf('44', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(dt_k2_tops_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( ( l1_pre_topc @ A ) & 
% 0.89/1.07         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.07       ( m1_subset_1 @
% 0.89/1.07         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.89/1.07  thf('45', plain,
% 0.89/1.07      (![X25 : $i, X26 : $i]:
% 0.89/1.07         (~ (l1_pre_topc @ X25)
% 0.89/1.07          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.89/1.07          | (m1_subset_1 @ (k2_tops_1 @ X25 @ X26) @ 
% 0.89/1.07             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.89/1.07  thf('46', plain,
% 0.89/1.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.89/1.07         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.07        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['44', '45'])).
% 0.89/1.07  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('48', plain,
% 0.89/1.07      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.89/1.07        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('demod', [status(thm)], ['46', '47'])).
% 0.89/1.07  thf('49', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(redefinition_k4_subset_1, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i]:
% 0.89/1.07     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.89/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.07       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.89/1.07  thf('50', plain,
% 0.89/1.07      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.89/1.07          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.89/1.07          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.89/1.07  thf('51', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.07            = (k2_xboole_0 @ sk_B @ X0))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['49', '50'])).
% 0.89/1.07  thf('52', plain,
% 0.89/1.07      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.89/1.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['48', '51'])).
% 0.89/1.07  thf('53', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(t65_tops_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( l1_pre_topc @ A ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.07           ( ( k2_pre_topc @ A @ B ) =
% 0.89/1.07             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.07  thf('54', plain,
% 0.89/1.07      (![X27 : $i, X28 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.89/1.07          | ((k2_pre_topc @ X28 @ X27)
% 0.89/1.07              = (k4_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 0.89/1.07                 (k2_tops_1 @ X28 @ X27)))
% 0.89/1.07          | ~ (l1_pre_topc @ X28))),
% 0.89/1.07      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.89/1.07  thf('55', plain,
% 0.89/1.07      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.07        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.07            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['53', '54'])).
% 0.89/1.07  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('57', plain,
% 0.89/1.07      (((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.07         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['55', '56'])).
% 0.89/1.07  thf('58', plain,
% 0.89/1.07      (((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['52', '57'])).
% 0.89/1.07  thf('59', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.07           = (k4_xboole_0 @ sk_B @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.07  thf('60', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07             (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('split', [status(esa)], ['2'])).
% 0.89/1.07  thf('61', plain,
% 0.89/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('sup+', [status(thm)], ['59', '60'])).
% 0.89/1.07  thf('62', plain,
% 0.89/1.07      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.89/1.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.89/1.07  thf(l32_xboole_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.89/1.07  thf('63', plain,
% 0.89/1.07      (![X0 : $i, X2 : $i]:
% 0.89/1.07         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.07      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.89/1.07  thf('64', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['62', '63'])).
% 0.89/1.07  thf(t39_xboole_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.07  thf('65', plain,
% 0.89/1.07      (![X8 : $i, X9 : $i]:
% 0.89/1.07         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.89/1.07           = (k2_xboole_0 @ X8 @ X9))),
% 0.89/1.07      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.07  thf('66', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.89/1.07           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['64', '65'])).
% 0.89/1.07  thf(t1_boole, axiom,
% 0.89/1.07    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.07  thf('67', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [t1_boole])).
% 0.89/1.07  thf('68', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['66', '67'])).
% 0.89/1.07  thf('69', plain,
% 0.89/1.07      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.89/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('sup+', [status(thm)], ['61', '68'])).
% 0.89/1.07  thf('70', plain,
% 0.89/1.07      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.89/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('sup+', [status(thm)], ['58', '69'])).
% 0.89/1.07  thf('71', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(t52_pre_topc, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( l1_pre_topc @ A ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.07           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.89/1.07             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.89/1.07               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.89/1.07  thf('72', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.89/1.07          | ~ (v2_pre_topc @ X24)
% 0.89/1.07          | ((k2_pre_topc @ X24 @ X23) != (X23))
% 0.89/1.07          | (v4_pre_topc @ X23 @ X24)
% 0.89/1.07          | ~ (l1_pre_topc @ X24))),
% 0.89/1.07      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.89/1.07  thf('73', plain,
% 0.89/1.07      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.07        | (v4_pre_topc @ sk_B @ sk_A)
% 0.89/1.07        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.89/1.07        | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.07  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('76', plain,
% 0.89/1.07      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.89/1.07  thf('77', plain,
% 0.89/1.07      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.89/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['70', '76'])).
% 0.89/1.07  thf('78', plain,
% 0.89/1.07      (((v4_pre_topc @ sk_B @ sk_A))
% 0.89/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['77'])).
% 0.89/1.07  thf('79', plain,
% 0.89/1.07      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.07      inference('split', [status(esa)], ['0'])).
% 0.89/1.07  thf('80', plain,
% 0.89/1.07      (~
% 0.89/1.07       (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.07       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['78', '79'])).
% 0.89/1.07  thf('81', plain, ($false),
% 0.89/1.07      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '80'])).
% 0.89/1.07  
% 0.89/1.07  % SZS output end Refutation
% 0.89/1.07  
% 0.89/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
