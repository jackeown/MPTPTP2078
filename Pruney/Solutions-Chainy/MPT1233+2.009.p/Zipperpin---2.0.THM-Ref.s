%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Se3MjJPdsu

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:50 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 159 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  596 (1040 expanded)
%              Number of equality atoms :   50 ( 107 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k1_subset_1 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = ( k3_subset_1 @ X7 @ ( k1_subset_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X7: $i] :
      ( X7
      = ( k3_subset_1 @ X7 @ ( k1_subset_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_subset_1 @ X8 @ X9 @ ( k3_subset_1 @ X8 @ X9 ) )
        = ( k2_subset_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_subset_1 @ X8 @ X9 @ ( k3_subset_1 @ X8 @ X9 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('18',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','43'])).

thf(t43_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_1])).

thf('45',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48','51'])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('55',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Se3MjJPdsu
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 209 iterations in 0.089s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.44/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.44/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.44/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(t4_subset_1, axiom,
% 0.44/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.61  thf('0', plain,
% 0.44/0.61      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.61  thf(t18_pre_topc, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_struct_0 @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( k4_subset_1 @
% 0.44/0.61               ( u1_struct_0 @ A ) @ B @ 
% 0.44/0.61               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.44/0.61             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      (![X20 : $i, X21 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.44/0.61          | ((k4_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.44/0.61              (k3_subset_1 @ (u1_struct_0 @ X21) @ X20)) = (k2_struct_0 @ X21))
% 0.44/0.61          | ~ (l1_struct_0 @ X21))),
% 0.44/0.61      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_struct_0 @ X0)
% 0.44/0.61          | ((k4_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.44/0.61              (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.44/0.61              = (k2_struct_0 @ X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.44/0.61  thf('3', plain, (![X3 : $i]: ((k1_subset_1 @ X3) = (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.44/0.61  thf(t22_subset_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      (![X7 : $i]:
% 0.44/0.61         ((k2_subset_1 @ X7) = (k3_subset_1 @ X7 @ (k1_subset_1 @ X7)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.44/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.44/0.61  thf('5', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (![X7 : $i]: ((X7) = (k3_subset_1 @ X7 @ (k1_subset_1 @ X7)))),
% 0.44/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.61  thf('7', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['3', '6'])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_struct_0 @ X0)
% 0.44/0.61          | ((k4_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.44/0.61              (u1_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['2', '7'])).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.61  thf(t25_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.61       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.44/0.61         ( k2_subset_1 @ A ) ) ))).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i]:
% 0.44/0.61         (((k4_subset_1 @ X8 @ X9 @ (k3_subset_1 @ X8 @ X9))
% 0.44/0.61            = (k2_subset_1 @ X8))
% 0.44/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.44/0.61  thf('11', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i]:
% 0.44/0.61         (((k4_subset_1 @ X8 @ X9 @ (k3_subset_1 @ X8 @ X9)) = (X8))
% 0.44/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.44/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k4_subset_1 @ X0 @ k1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.44/0.61           = (X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['9', '12'])).
% 0.44/0.61  thf('14', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['3', '6'])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (![X0 : $i]: ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['8', '15'])).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['8', '15'])).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.61  thf(cc2_pre_topc, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (![X17 : $i, X18 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.44/0.61          | (v4_pre_topc @ X17 @ X18)
% 0.44/0.61          | ~ (v1_xboole_0 @ X17)
% 0.44/0.61          | ~ (l1_pre_topc @ X18)
% 0.44/0.61          | ~ (v2_pre_topc @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v2_pre_topc @ X0)
% 0.44/0.61          | ~ (l1_pre_topc @ X0)
% 0.44/0.61          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.61          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.61  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v2_pre_topc @ X0)
% 0.44/0.61          | ~ (l1_pre_topc @ X0)
% 0.44/0.61          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.61  thf(t52_pre_topc, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_pre_topc @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.44/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.44/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.44/0.61  thf('24', plain,
% 0.44/0.61      (![X22 : $i, X23 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.44/0.61          | ~ (v4_pre_topc @ X22 @ X23)
% 0.44/0.61          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.44/0.61          | ~ (l1_pre_topc @ X23))),
% 0.44/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.44/0.61  thf('25', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_pre_topc @ X0)
% 0.44/0.61          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.61          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('26', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_pre_topc @ X0)
% 0.44/0.61          | ~ (v2_pre_topc @ X0)
% 0.44/0.61          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.61          | ~ (l1_pre_topc @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['22', '25'])).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.61          | ~ (v2_pre_topc @ X0)
% 0.44/0.61          | ~ (l1_pre_topc @ X0))),
% 0.44/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.44/0.61  thf(d10_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.61  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.44/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.61  thf(t3_subset, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      (![X11 : $i, X13 : $i]:
% 0.44/0.61         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.44/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.61  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.61  thf(d1_tops_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_pre_topc @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61           ( ( k1_tops_1 @ A @ B ) =
% 0.44/0.61             ( k3_subset_1 @
% 0.44/0.61               ( u1_struct_0 @ A ) @ 
% 0.44/0.61               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      (![X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.61          | ((k1_tops_1 @ X25 @ X24)
% 0.44/0.61              = (k3_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.44/0.61                 (k2_pre_topc @ X25 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24))))
% 0.44/0.61          | ~ (l1_pre_topc @ X25))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_pre_topc @ X0)
% 0.44/0.61          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.44/0.61              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.44/0.61                 (k2_pre_topc @ X0 @ 
% 0.44/0.61                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.61  thf(involutiveness_k3_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X5 : $i, X6 : $i]:
% 0.44/0.61         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.44/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.44/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.61  thf('37', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['3', '6'])).
% 0.44/0.61  thf('38', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.61  thf('39', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_pre_topc @ X0)
% 0.44/0.61          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.44/0.61              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.44/0.61                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['33', '38'])).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.44/0.61            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.44/0.61          | ~ (l1_pre_topc @ X0)
% 0.44/0.61          | ~ (v2_pre_topc @ X0)
% 0.44/0.61          | ~ (l1_pre_topc @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['27', '39'])).
% 0.44/0.61  thf('41', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['3', '6'])).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.44/0.61          | ~ (l1_pre_topc @ X0)
% 0.44/0.61          | ~ (v2_pre_topc @ X0)
% 0.44/0.61          | ~ (l1_pre_topc @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v2_pre_topc @ X0)
% 0.44/0.61          | ~ (l1_pre_topc @ X0)
% 0.44/0.61          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.44/0.61  thf('44', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.44/0.61          | ~ (l1_struct_0 @ X0)
% 0.44/0.61          | ~ (l1_pre_topc @ X0)
% 0.44/0.61          | ~ (v2_pre_topc @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['17', '43'])).
% 0.44/0.61  thf(t43_tops_1, conjecture,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.61       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i]:
% 0.44/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.61          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.44/0.61  thf('45', plain,
% 0.44/0.61      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.44/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.61  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(dt_l1_pre_topc, axiom,
% 0.44/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.61  thf('50', plain,
% 0.44/0.61      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.44/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.61  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.61  thf('52', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['46', '47', '48', '51'])).
% 0.44/0.61  thf('53', plain,
% 0.44/0.61      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '52'])).
% 0.44/0.61  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.61  thf('55', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.44/0.61  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
