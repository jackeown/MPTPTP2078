%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dfB82TUntb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:21 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 281 expanded)
%              Number of leaves         :   28 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  730 (3737 expanded)
%              Number of equality atoms :   36 ( 139 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t75_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
              = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('24',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','27'])).

thf('29',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','27'])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','27'])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','27'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X24 @ ( k2_tops_1 @ X24 @ ( k2_tops_1 @ X24 @ X23 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X10 @ X12 )
        = ( k4_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','28','29','30','31','37','40','50'])).

thf('52',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dfB82TUntb
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 486 iterations in 0.237s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.72  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.52/0.72  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.52/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.52/0.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.52/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.72  thf(t75_tops_1, conjecture,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.52/0.72             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i]:
% 0.52/0.72        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.72          ( ![B:$i]:
% 0.52/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.52/0.72                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(dt_k2_tops_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( l1_pre_topc @ A ) & 
% 0.52/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.72       ( m1_subset_1 @
% 0.52/0.72         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (![X17 : $i, X18 : $i]:
% 0.52/0.72         (~ (l1_pre_topc @ X17)
% 0.52/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.52/0.72          | (m1_subset_1 @ (k2_tops_1 @ X17 @ X18) @ 
% 0.52/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.52/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X17 : $i, X18 : $i]:
% 0.52/0.72         (~ (l1_pre_topc @ X17)
% 0.52/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.52/0.72          | (m1_subset_1 @ (k2_tops_1 @ X17 @ X18) @ 
% 0.52/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.52/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.72  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf(dt_k2_pre_topc, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( l1_pre_topc @ A ) & 
% 0.52/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.72       ( m1_subset_1 @
% 0.52/0.72         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (![X13 : $i, X14 : $i]:
% 0.52/0.72         (~ (l1_pre_topc @ X13)
% 0.52/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.52/0.72          | (m1_subset_1 @ (k2_pre_topc @ X13 @ X14) @ 
% 0.52/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      (((m1_subset_1 @ 
% 0.52/0.72         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.52/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.72  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      ((m1_subset_1 @ 
% 0.52/0.72        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['10', '11'])).
% 0.52/0.72  thf(l78_tops_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( l1_pre_topc @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( k2_tops_1 @ A @ B ) =
% 0.52/0.72             ( k7_subset_1 @
% 0.52/0.72               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.52/0.72               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X21 : $i, X22 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.52/0.72          | ((k2_tops_1 @ X22 @ X21)
% 0.52/0.72              = (k7_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.52/0.72                 (k2_pre_topc @ X22 @ X21) @ (k1_tops_1 @ X22 @ X21)))
% 0.52/0.72          | ~ (l1_pre_topc @ X22))),
% 0.52/0.72      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.72        | ((k2_tops_1 @ sk_A @ 
% 0.52/0.72            (k2_pre_topc @ sk_A @ 
% 0.52/0.72             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.52/0.72            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.72               (k2_pre_topc @ sk_A @ 
% 0.52/0.72                (k2_pre_topc @ sk_A @ 
% 0.52/0.72                 (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 0.52/0.72               (k1_tops_1 @ sk_A @ 
% 0.52/0.72                (k2_pre_topc @ sk_A @ 
% 0.52/0.72                 (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.72  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      (((k2_tops_1 @ sk_A @ 
% 0.52/0.72         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.52/0.72         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.72            (k2_pre_topc @ sk_A @ 
% 0.52/0.72             (k2_pre_topc @ sk_A @ 
% 0.52/0.72              (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 0.52/0.72            (k1_tops_1 @ sk_A @ 
% 0.52/0.72             (k2_pre_topc @ sk_A @ 
% 0.52/0.72              (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 0.52/0.72      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf(t52_pre_topc, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( l1_pre_topc @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.52/0.72             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.52/0.72               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.52/0.72          | ~ (v4_pre_topc @ X15 @ X16)
% 0.52/0.72          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 0.52/0.72          | ~ (l1_pre_topc @ X16))),
% 0.52/0.72      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.72        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.52/0.72             sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.72  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      ((((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72          = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.52/0.72             sk_A))),
% 0.52/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf(fc11_tops_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.52/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.72       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      (![X19 : $i, X20 : $i]:
% 0.52/0.72         (~ (l1_pre_topc @ X19)
% 0.52/0.72          | ~ (v2_pre_topc @ X19)
% 0.52/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | (v4_pre_topc @ (k2_tops_1 @ X19 @ X20) @ X19))),
% 0.52/0.72      inference('cnf', [status(esa)], [fc11_tops_1])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.52/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.52/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.72  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('27', plain,
% 0.52/0.72      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.52/0.72      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['21', '27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['21', '27'])).
% 0.52/0.72  thf('30', plain,
% 0.52/0.72      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['21', '27'])).
% 0.52/0.72  thf('31', plain,
% 0.52/0.72      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['21', '27'])).
% 0.52/0.72  thf('32', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(l80_tops_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.52/0.72             ( k1_xboole_0 ) ) ) ) ))).
% 0.52/0.72  thf('33', plain,
% 0.52/0.72      (![X23 : $i, X24 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.52/0.72          | ((k1_tops_1 @ X24 @ (k2_tops_1 @ X24 @ (k2_tops_1 @ X24 @ X23)))
% 0.52/0.72              = (k1_xboole_0))
% 0.52/0.72          | ~ (l1_pre_topc @ X24)
% 0.52/0.72          | ~ (v2_pre_topc @ X24))),
% 0.52/0.72      inference('cnf', [status(esa)], [l80_tops_1])).
% 0.52/0.72  thf('34', plain,
% 0.52/0.72      ((~ (v2_pre_topc @ sk_A)
% 0.52/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.72        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72            = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.72  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf(redefinition_k7_subset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.72       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.52/0.72          | ((k7_subset_1 @ X11 @ X10 @ X12) = (k4_xboole_0 @ X10 @ X12)))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.52/0.72  thf('40', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.72           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 0.52/0.72           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.72  thf(d10_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.72  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.72      inference('simplify', [status(thm)], ['41'])).
% 0.52/0.72  thf(l32_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.72  thf('43', plain,
% 0.52/0.72      (![X3 : $i, X5 : $i]:
% 0.52/0.72         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.52/0.72      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.72  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.72  thf(t48_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.72  thf('45', plain,
% 0.52/0.72      (![X8 : $i, X9 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.52/0.72           = (k3_xboole_0 @ X8 @ X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.72  thf('46', plain,
% 0.52/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['44', '45'])).
% 0.52/0.72  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.72      inference('simplify', [status(thm)], ['41'])).
% 0.52/0.72  thf(t28_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.72  thf('48', plain,
% 0.52/0.72      (![X6 : $i, X7 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.52/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.72  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.72  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['46', '49'])).
% 0.52/0.72  thf('51', plain,
% 0.52/0.72      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)],
% 0.52/0.72                ['16', '28', '29', '30', '31', '37', '40', '50'])).
% 0.52/0.72  thf('52', plain,
% 0.52/0.72      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('53', plain, ($false),
% 0.52/0.72      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
