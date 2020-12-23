%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t1h5q0KPJg

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:15 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  170 (1488 expanded)
%              Number of leaves         :   29 ( 452 expanded)
%              Depth                    :   23
%              Number of atoms          : 1427 (13773 expanded)
%              Number of equality atoms :  109 ( 936 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t84_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( ( k1_tops_1 @ A @ B )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tops_1])).

thf('0',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tops_1 @ X19 @ X20 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('13',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('27',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','26'])).

thf('28',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('33',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('52',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('61',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('74',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','65','72','73'])).

thf('75',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('77',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ X15 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_pre_topc @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['77','83'])).

thf('85',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('88',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('93',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('95',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('96',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('98',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('101',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('103',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('110',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('112',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('114',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('116',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('119',plain,
    ( ( k1_xboole_0
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('121',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','119','120'])).

thf('122',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('124',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
       != ( k2_struct_0 @ X18 ) )
      | ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v2_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('135',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('138',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','91','92','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t1h5q0KPJg
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 884 iterations in 0.325s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.53/0.74  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.53/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.53/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.74  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.53/0.74  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.53/0.74  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(t84_tops_1, conjecture,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( l1_pre_topc @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74           ( ( v2_tops_1 @ B @ A ) <=>
% 0.53/0.74             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i]:
% 0.53/0.74        ( ( l1_pre_topc @ A ) =>
% 0.53/0.74          ( ![B:$i]:
% 0.53/0.74            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74              ( ( v2_tops_1 @ B @ A ) <=>
% 0.53/0.74                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.53/0.74        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('split', [status(esa)], ['2'])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(d4_tops_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( l1_pre_topc @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74           ( ( v2_tops_1 @ B @ A ) <=>
% 0.53/0.74             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (![X19 : $i, X20 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.53/0.74          | ~ (v2_tops_1 @ X19 @ X20)
% 0.53/0.74          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.53/0.74          | ~ (l1_pre_topc @ X20))),
% 0.53/0.74      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.74        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.53/0.74        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.53/0.74  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(d5_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.53/0.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.74  thf(d3_struct_0, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X11 : $i]:
% 0.53/0.74         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.53/0.74        | ~ (l1_struct_0 @ sk_A))),
% 0.53/0.74      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.74  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(dt_l1_pre_topc, axiom,
% 0.53/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.53/0.74  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '16'])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X11 : $i]:
% 0.53/0.74         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.53/0.74        | ~ (l1_struct_0 @ sk_A))),
% 0.53/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.53/0.74  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.53/0.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['10', '25'])).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.53/0.74        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['6', '7', '26'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['3', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(dt_k3_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.53/0.74          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['10', '25'])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.53/0.74  thf(d3_tops_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( l1_pre_topc @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74           ( ( v1_tops_1 @ B @ A ) <=>
% 0.53/0.74             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.53/0.74          | ~ (v1_tops_1 @ X17 @ X18)
% 0.53/0.74          | ((k2_pre_topc @ X18 @ X17) = (k2_struct_0 @ X18))
% 0.53/0.74          | ~ (l1_pre_topc @ X18))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.74        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.53/0.74            = (k2_struct_0 @ sk_A))
% 0.53/0.74        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.53/0.74          = (k2_struct_0 @ sk_A))
% 0.53/0.74        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['35', '36'])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.53/0.74          = (k2_struct_0 @ sk_A)))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['28', '37'])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.53/0.74  thf(dt_k2_pre_topc, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( l1_pre_topc @ A ) & 
% 0.53/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.74       ( m1_subset_1 @
% 0.53/0.74         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i]:
% 0.53/0.74         (~ (l1_pre_topc @ X12)
% 0.53/0.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.53/0.74          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.53/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (((m1_subset_1 @ 
% 0.53/0.74         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.53/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.74  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      ((m1_subset_1 @ 
% 0.53/0.74        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.53/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['38', '43'])).
% 0.53/0.74  thf(involutiveness_k3_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X6 : $i, X7 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.53/0.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.53/0.74      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.53/0.74          = (k2_struct_0 @ sk_A)))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.53/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['38', '43'])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      (![X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.53/0.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.74  thf('49', plain,
% 0.53/0.74      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.53/0.74          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X11 : $i]:
% 0.53/0.74         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.53/0.74          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.53/0.74           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.53/0.74         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['50', '51'])).
% 0.53/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.53/0.74  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.74  thf(t3_subset, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      (![X8 : $i, X10 : $i]:
% 0.53/0.74         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.53/0.74          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['55', '56'])).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      (![X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.53/0.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.74  thf('60', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.53/0.74  thf(t3_boole, axiom,
% 0.53/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.74  thf('61', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.74  thf('62', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.74  thf('63', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['57', '62'])).
% 0.53/0.74  thf('64', plain,
% 0.53/0.74      (![X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.53/0.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.74  thf('65', plain,
% 0.53/0.74      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['63', '64'])).
% 0.53/0.74  thf('66', plain,
% 0.53/0.74      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['63', '64'])).
% 0.53/0.74  thf('67', plain,
% 0.53/0.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.74  thf('68', plain,
% 0.53/0.74      (![X6 : $i, X7 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.53/0.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.53/0.74      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.53/0.74  thf('69', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['67', '68'])).
% 0.53/0.74  thf('70', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.74  thf('71', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['69', '70'])).
% 0.53/0.74  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['66', '71'])).
% 0.53/0.74  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('74', plain,
% 0.53/0.74      ((((k1_xboole_0)
% 0.53/0.74          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['52', '65', '72', '73'])).
% 0.53/0.74  thf('75', plain,
% 0.53/0.74      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.53/0.74          = (k1_xboole_0)))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['49', '74'])).
% 0.53/0.74  thf('76', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.74  thf('77', plain,
% 0.53/0.74      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['46', '75', '76'])).
% 0.53/0.74  thf('78', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(d1_tops_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( l1_pre_topc @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74           ( ( k1_tops_1 @ A @ B ) =
% 0.53/0.74             ( k3_subset_1 @
% 0.53/0.74               ( u1_struct_0 @ A ) @ 
% 0.53/0.74               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.53/0.74  thf('79', plain,
% 0.53/0.74      (![X15 : $i, X16 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.53/0.74          | ((k1_tops_1 @ X16 @ X15)
% 0.53/0.74              = (k3_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.53/0.74                 (k2_pre_topc @ X16 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15))))
% 0.53/0.74          | ~ (l1_pre_topc @ X16))),
% 0.53/0.74      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.53/0.74  thf('80', plain,
% 0.53/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.74        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74               (k2_pre_topc @ sk_A @ 
% 0.53/0.74                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['78', '79'])).
% 0.53/0.74  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('82', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['10', '25'])).
% 0.53/0.74  thf('83', plain,
% 0.53/0.74      (((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.53/0.74      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.53/0.74  thf('84', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.53/0.74             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['77', '83'])).
% 0.53/0.74  thf('85', plain,
% 0.53/0.74      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.53/0.74          = (k2_struct_0 @ sk_A)))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['28', '37'])).
% 0.53/0.74  thf('86', plain,
% 0.53/0.74      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['63', '64'])).
% 0.53/0.74  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['66', '71'])).
% 0.53/0.74  thf('88', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.53/0.74         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.53/0.74  thf('89', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.53/0.74         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('90', plain,
% 0.53/0.74      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.53/0.74         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['88', '89'])).
% 0.53/0.74  thf('91', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('simplify', [status(thm)], ['90'])).
% 0.53/0.74  thf('92', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('split', [status(esa)], ['2'])).
% 0.53/0.74  thf('93', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['2'])).
% 0.53/0.74  thf('94', plain,
% 0.53/0.74      ((m1_subset_1 @ 
% 0.53/0.74        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.53/0.74  thf('95', plain,
% 0.53/0.74      (![X6 : $i, X7 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.53/0.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.53/0.74      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.53/0.74  thf('96', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.74         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['94', '95'])).
% 0.53/0.74  thf('97', plain,
% 0.53/0.74      (((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.53/0.74      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.53/0.74  thf('98', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.53/0.74         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.53/0.74      inference('demod', [status(thm)], ['96', '97'])).
% 0.53/0.74  thf('99', plain,
% 0.53/0.74      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.53/0.74          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['93', '98'])).
% 0.53/0.74  thf('100', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.74  thf('101', plain,
% 0.53/0.74      ((((u1_struct_0 @ sk_A)
% 0.53/0.74          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['99', '100'])).
% 0.53/0.74  thf('102', plain,
% 0.53/0.74      ((((u1_struct_0 @ sk_A)
% 0.53/0.74          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['99', '100'])).
% 0.53/0.74  thf('103', plain,
% 0.53/0.74      (![X11 : $i]:
% 0.53/0.74         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.53/0.74  thf('104', plain,
% 0.53/0.74      ((m1_subset_1 @ 
% 0.53/0.74        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.53/0.74  thf('105', plain,
% 0.53/0.74      (((m1_subset_1 @ 
% 0.53/0.74         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.53/0.74         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.53/0.74        | ~ (l1_struct_0 @ sk_A))),
% 0.53/0.74      inference('sup+', [status(thm)], ['103', '104'])).
% 0.53/0.74  thf('106', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('107', plain,
% 0.53/0.74      ((m1_subset_1 @ 
% 0.53/0.74        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['105', '106'])).
% 0.53/0.74  thf('108', plain,
% 0.53/0.74      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['102', '107'])).
% 0.53/0.74  thf('109', plain,
% 0.53/0.74      (![X6 : $i, X7 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.53/0.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.53/0.74      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.53/0.74  thf('110', plain,
% 0.53/0.74      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.53/0.74          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.53/0.74          = (u1_struct_0 @ sk_A)))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['108', '109'])).
% 0.53/0.74  thf('111', plain,
% 0.53/0.74      ((((u1_struct_0 @ sk_A)
% 0.53/0.74          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['99', '100'])).
% 0.53/0.74  thf('112', plain,
% 0.53/0.74      (![X11 : $i]:
% 0.53/0.74         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.53/0.74  thf('113', plain,
% 0.53/0.74      (((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.74            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.53/0.74      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.53/0.74  thf('114', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.53/0.74             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.74        | ~ (l1_struct_0 @ sk_A))),
% 0.53/0.74      inference('sup+', [status(thm)], ['112', '113'])).
% 0.53/0.74  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('116', plain,
% 0.53/0.74      (((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.53/0.74            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.53/0.74      inference('demod', [status(thm)], ['114', '115'])).
% 0.53/0.74  thf('117', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.74          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['111', '116'])).
% 0.53/0.74  thf('118', plain,
% 0.53/0.74      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['2'])).
% 0.53/0.74  thf('119', plain,
% 0.53/0.74      ((((k1_xboole_0)
% 0.53/0.74          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['117', '118'])).
% 0.53/0.74  thf('120', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.74  thf('121', plain,
% 0.53/0.74      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['110', '119', '120'])).
% 0.53/0.74  thf('122', plain,
% 0.53/0.74      ((((k2_struct_0 @ sk_A)
% 0.53/0.74          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['101', '121'])).
% 0.53/0.74  thf('123', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.53/0.74  thf('124', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.53/0.74          | ((k2_pre_topc @ X18 @ X17) != (k2_struct_0 @ X18))
% 0.53/0.74          | (v1_tops_1 @ X17 @ X18)
% 0.53/0.74          | ~ (l1_pre_topc @ X18))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.53/0.74  thf('125', plain,
% 0.53/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.74        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.53/0.74        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.53/0.74            != (k2_struct_0 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['123', '124'])).
% 0.53/0.74  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('127', plain,
% 0.53/0.74      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.53/0.74        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.53/0.74            != (k2_struct_0 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['125', '126'])).
% 0.53/0.74  thf('128', plain,
% 0.53/0.74      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.53/0.74         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['122', '127'])).
% 0.53/0.74  thf('129', plain,
% 0.53/0.74      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['128'])).
% 0.53/0.74  thf('130', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('131', plain,
% 0.53/0.74      (![X19 : $i, X20 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.53/0.74          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.53/0.74          | (v2_tops_1 @ X19 @ X20)
% 0.53/0.74          | ~ (l1_pre_topc @ X20))),
% 0.53/0.74      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.53/0.74  thf('132', plain,
% 0.53/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.74        | (v2_tops_1 @ sk_B @ sk_A)
% 0.53/0.74        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['130', '131'])).
% 0.53/0.74  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('134', plain,
% 0.53/0.74      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['10', '25'])).
% 0.53/0.74  thf('135', plain,
% 0.53/0.74      (((v2_tops_1 @ sk_B @ sk_A)
% 0.53/0.74        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.53/0.74  thf('136', plain,
% 0.53/0.74      (((v2_tops_1 @ sk_B @ sk_A))
% 0.53/0.74         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['129', '135'])).
% 0.53/0.74  thf('137', plain,
% 0.53/0.74      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('138', plain,
% 0.53/0.74      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['136', '137'])).
% 0.53/0.74  thf('139', plain, ($false),
% 0.53/0.74      inference('sat_resolution*', [status(thm)], ['1', '91', '92', '138'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
