%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TrRwvOHXsD

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:14 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 887 expanded)
%              Number of leaves         :   34 ( 273 expanded)
%              Depth                    :   21
%              Number of atoms          : 1382 (8308 expanded)
%              Number of equality atoms :  100 ( 540 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','26'])).

thf('28',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('34',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('37',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('50',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('53',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('56',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('60',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('61',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('62',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('72',plain,(
    ! [X3: $i] :
      ( ( k1_subset_1 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = ( k3_subset_1 @ X12 @ ( k1_subset_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('74',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('75',plain,(
    ! [X12: $i] :
      ( X12
      = ( k3_subset_1 @ X12 @ ( k1_subset_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('79',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','77','78'])).

thf('80',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('82',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('89',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('91',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('93',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('99',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('101',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('102',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('105',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('108',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('109',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('113',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('116',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('118',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
       != ( k2_struct_0 @ X20 ) )
      | ( v1_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('129',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','129'])).

thf('131',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('132',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','96','97','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TrRwvOHXsD
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 1276 iterations in 0.422s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.68/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.68/0.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.88  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.68/0.88  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.68/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.68/0.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(t84_tops_1, conjecture,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( ( v2_tops_1 @ B @ A ) <=>
% 0.68/0.88             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i]:
% 0.68/0.88        ( ( l1_pre_topc @ A ) =>
% 0.68/0.88          ( ![B:$i]:
% 0.68/0.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88              ( ( v2_tops_1 @ B @ A ) <=>
% 0.68/0.88                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.68/0.88        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.68/0.88       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('split', [status(esa)], ['0'])).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('split', [status(esa)], ['2'])).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(d4_tops_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( ( v2_tops_1 @ B @ A ) <=>
% 0.68/0.88             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X21 : $i, X22 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.68/0.88          | ~ (v2_tops_1 @ X21 @ X22)
% 0.68/0.88          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.68/0.88          | ~ (l1_pre_topc @ X22))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.68/0.88        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(d5_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.68/0.88          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf(d3_struct_0, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X13 : $i]:
% 0.68/0.88         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.68/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['11', '12'])).
% 0.68/0.88  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(dt_l1_pre_topc, axiom,
% 0.68/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.88  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['13', '16'])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['10', '17'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X13 : $i]:
% 0.68/0.88         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.68/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['19', '20'])).
% 0.68/0.88  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.68/0.88          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['18', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.68/0.88        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '7', '26'])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '27'])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (![X13 : $i]:
% 0.68/0.88         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(dt_k3_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (![X8 : $i, X9 : $i]:
% 0.68/0.88         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.68/0.88          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['32', '33'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['29', '34'])).
% 0.68/0.88  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.88  thf(d3_tops_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( ( v1_tops_1 @ B @ A ) <=>
% 0.68/0.88             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      (![X19 : $i, X20 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.68/0.88          | ~ (v1_tops_1 @ X19 @ X20)
% 0.68/0.88          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.68/0.88          | ~ (l1_pre_topc @ X20))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.88            = (k2_struct_0 @ sk_A))
% 0.68/0.88        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['37', '38'])).
% 0.68/0.88  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.88          = (k2_struct_0 @ sk_A))
% 0.68/0.88        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['39', '40'])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.88          = (k2_struct_0 @ sk_A)))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['28', '41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.88  thf(dt_k2_pre_topc, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( l1_pre_topc @ A ) & 
% 0.68/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88       ( m1_subset_1 @
% 0.68/0.88         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X14)
% 0.68/0.88          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.68/0.88          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.68/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (((m1_subset_1 @ 
% 0.68/0.88         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['43', '44'])).
% 0.68/0.88  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      ((m1_subset_1 @ 
% 0.68/0.88        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['45', '46'])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['42', '47'])).
% 0.68/0.88  thf(involutiveness_k3_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.68/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.68/0.88      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.68/0.88          = (k2_struct_0 @ sk_A)))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['42', '47'])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.68/0.88          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.68/0.88          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['51', '52'])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      (![X13 : $i]:
% 0.68/0.88         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.68/0.88          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['51', '52'])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.68/0.88           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.68/0.88         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['54', '55'])).
% 0.68/0.88  thf(t1_boole, axiom,
% 0.68/0.88    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.88  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_boole])).
% 0.68/0.88  thf(t46_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      (![X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X2)) = (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.68/0.88  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['57', '58'])).
% 0.68/0.88  thf(dt_k2_subset_1, axiom,
% 0.68/0.88    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.68/0.88  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.68/0.88  thf('61', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.88  thf('62', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.68/0.88      inference('demod', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      (![X8 : $i, X9 : $i]:
% 0.68/0.88         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.68/0.88          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['62', '63'])).
% 0.68/0.88  thf('65', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.68/0.88      inference('demod', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.68/0.88          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('67', plain,
% 0.68/0.88      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['65', '66'])).
% 0.68/0.88  thf('68', plain,
% 0.68/0.88      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['64', '67'])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['59', '68'])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.68/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.68/0.88      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.68/0.88  thf('71', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['69', '70'])).
% 0.68/0.88  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.68/0.88  thf('72', plain, (![X3 : $i]: ((k1_subset_1 @ X3) = (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.68/0.88  thf(t22_subset_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      (![X12 : $i]:
% 0.68/0.88         ((k2_subset_1 @ X12) = (k3_subset_1 @ X12 @ (k1_subset_1 @ X12)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.68/0.88  thf('74', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (![X12 : $i]: ((X12) = (k3_subset_1 @ X12 @ (k1_subset_1 @ X12)))),
% 0.68/0.88      inference('demod', [status(thm)], ['73', '74'])).
% 0.68/0.88  thf('76', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['72', '75'])).
% 0.68/0.88  thf('77', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['71', '76'])).
% 0.68/0.88  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      ((((k1_xboole_0)
% 0.68/0.88          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['56', '77', '78'])).
% 0.68/0.88  thf('80', plain,
% 0.68/0.88      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.68/0.88          = (k1_xboole_0)))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['53', '79'])).
% 0.68/0.88  thf('81', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['72', '75'])).
% 0.68/0.88  thf('82', plain,
% 0.68/0.88      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['50', '80', '81'])).
% 0.68/0.88  thf('83', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(d1_tops_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( ( k1_tops_1 @ A @ B ) =
% 0.68/0.88             ( k3_subset_1 @
% 0.68/0.88               ( u1_struct_0 @ A ) @ 
% 0.68/0.88               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.68/0.88  thf('84', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.68/0.88          | ((k1_tops_1 @ X18 @ X17)
% 0.68/0.88              = (k3_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.68/0.88                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 0.68/0.88          | ~ (l1_pre_topc @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.68/0.88  thf('85', plain,
% 0.68/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.68/0.88            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88               (k2_pre_topc @ sk_A @ 
% 0.68/0.88                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['83', '84'])).
% 0.68/0.88  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('87', plain,
% 0.68/0.88      (((k1_tops_1 @ sk_A @ sk_B)
% 0.68/0.88         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.68/0.88      inference('demod', [status(thm)], ['85', '86'])).
% 0.68/0.88  thf('88', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['18', '25'])).
% 0.68/0.88  thf('89', plain,
% 0.68/0.88      (((k1_tops_1 @ sk_A @ sk_B)
% 0.68/0.88         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.68/0.88      inference('demod', [status(thm)], ['87', '88'])).
% 0.68/0.88  thf('90', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.68/0.88          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['82', '89'])).
% 0.68/0.88  thf('91', plain,
% 0.68/0.88      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.88          = (k2_struct_0 @ sk_A)))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['28', '41'])).
% 0.68/0.88  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['71', '76'])).
% 0.68/0.88  thf('93', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.68/0.88         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.68/0.88  thf('94', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.68/0.88         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('split', [status(esa)], ['0'])).
% 0.68/0.88  thf('95', plain,
% 0.68/0.88      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.68/0.88         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.68/0.88             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['93', '94'])).
% 0.68/0.88  thf('96', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.68/0.88       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('simplify', [status(thm)], ['95'])).
% 0.68/0.88  thf('97', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.68/0.88       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('split', [status(esa)], ['2'])).
% 0.68/0.88  thf('98', plain,
% 0.68/0.88      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.68/0.88         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('split', [status(esa)], ['2'])).
% 0.68/0.88  thf('99', plain,
% 0.68/0.88      (![X13 : $i]:
% 0.68/0.88         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.88  thf('100', plain,
% 0.68/0.88      ((m1_subset_1 @ 
% 0.68/0.88        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['45', '46'])).
% 0.68/0.88  thf('101', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.68/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.68/0.88      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.68/0.88  thf('102', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.68/0.88         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['100', '101'])).
% 0.68/0.88  thf('103', plain,
% 0.68/0.88      ((m1_subset_1 @ 
% 0.68/0.88        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['45', '46'])).
% 0.68/0.88  thf('104', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.68/0.88          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('105', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.68/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['103', '104'])).
% 0.68/0.88  thf('106', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.68/0.88         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.68/0.88      inference('demod', [status(thm)], ['102', '105'])).
% 0.68/0.88  thf('107', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.68/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['103', '104'])).
% 0.68/0.88  thf('108', plain,
% 0.68/0.88      (((k1_tops_1 @ sk_A @ sk_B)
% 0.68/0.88         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.68/0.88      inference('demod', [status(thm)], ['87', '88'])).
% 0.68/0.88  thf('109', plain,
% 0.68/0.88      (((k1_tops_1 @ sk_A @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.88            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['107', '108'])).
% 0.68/0.88  thf('110', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.68/0.88         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.68/0.88      inference('demod', [status(thm)], ['106', '109'])).
% 0.68/0.88  thf('111', plain,
% 0.68/0.88      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.68/0.88          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.68/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['99', '110'])).
% 0.68/0.88  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf('113', plain,
% 0.68/0.88      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.68/0.88         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.68/0.88      inference('demod', [status(thm)], ['111', '112'])).
% 0.68/0.88  thf('114', plain,
% 0.68/0.88      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.68/0.88          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.68/0.88         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['98', '113'])).
% 0.68/0.88  thf('115', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['72', '75'])).
% 0.68/0.88  thf('116', plain,
% 0.68/0.88      ((((k2_struct_0 @ sk_A)
% 0.68/0.88          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.68/0.88         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('demod', [status(thm)], ['114', '115'])).
% 0.68/0.88  thf('117', plain,
% 0.68/0.88      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.88  thf('118', plain,
% 0.68/0.88      (![X19 : $i, X20 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.68/0.88          | ((k2_pre_topc @ X20 @ X19) != (k2_struct_0 @ X20))
% 0.68/0.88          | (v1_tops_1 @ X19 @ X20)
% 0.68/0.88          | ~ (l1_pre_topc @ X20))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.68/0.88  thf('119', plain,
% 0.68/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.88            != (k2_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['117', '118'])).
% 0.68/0.88  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('121', plain,
% 0.68/0.88      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.88            != (k2_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['119', '120'])).
% 0.68/0.88  thf('122', plain,
% 0.68/0.88      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.68/0.88         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.68/0.88         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['116', '121'])).
% 0.68/0.88  thf('123', plain,
% 0.68/0.88      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.68/0.88         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['122'])).
% 0.68/0.88  thf('124', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('125', plain,
% 0.68/0.88      (![X21 : $i, X22 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.68/0.88          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.68/0.88          | (v2_tops_1 @ X21 @ X22)
% 0.68/0.88          | ~ (l1_pre_topc @ X22))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.68/0.88  thf('126', plain,
% 0.68/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | (v2_tops_1 @ sk_B @ sk_A)
% 0.68/0.88        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['124', '125'])).
% 0.68/0.88  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('128', plain,
% 0.68/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.68/0.88         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['18', '25'])).
% 0.68/0.88  thf('129', plain,
% 0.68/0.88      (((v2_tops_1 @ sk_B @ sk_A)
% 0.68/0.88        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.68/0.88  thf('130', plain,
% 0.68/0.88      (((v2_tops_1 @ sk_B @ sk_A))
% 0.68/0.88         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['123', '129'])).
% 0.68/0.88  thf('131', plain,
% 0.68/0.88      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('split', [status(esa)], ['0'])).
% 0.68/0.88  thf('132', plain,
% 0.68/0.88      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.68/0.88       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['130', '131'])).
% 0.68/0.88  thf('133', plain, ($false),
% 0.68/0.88      inference('sat_resolution*', [status(thm)], ['1', '96', '97', '132'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
