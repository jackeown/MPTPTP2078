%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2kww1Nma7i

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:14 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 450 expanded)
%              Number of leaves         :   29 ( 142 expanded)
%              Depth                    :   24
%              Number of atoms          : 1221 (4241 expanded)
%              Number of equality atoms :   91 ( 287 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf('8',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ X15 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_pre_topc @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','28'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('35',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('50',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('56',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('70',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('72',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('79',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('85',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('87',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('91',plain,
    ( ( k1_xboole_0
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('93',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','91','92'])).

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
       != ( k2_struct_0 @ X18 ) )
      | ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','97'])).

thf('99',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('100',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('102',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v2_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('112',plain,
    ( ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','112'])).

thf('114',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2kww1Nma7i
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 997 iterations in 0.330s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.58/0.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.78  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.58/0.78  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.58/0.78  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.58/0.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.78  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.78  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.58/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.78  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.58/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.78  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.58/0.78  thf(t84_tops_1, conjecture,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.78             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i]:
% 0.58/0.78        ( ( l1_pre_topc @ A ) =>
% 0.58/0.78          ( ![B:$i]:
% 0.58/0.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78              ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.78                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.58/0.78  thf('0', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.58/0.78        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('1', plain,
% 0.58/0.78      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.58/0.78       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('2', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('4', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(d4_tops_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.78             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.58/0.78  thf('5', plain,
% 0.58/0.78      (![X19 : $i, X20 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.58/0.78          | ~ (v2_tops_1 @ X19 @ X20)
% 0.58/0.78          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.58/0.78          | ~ (l1_pre_topc @ X20))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.58/0.78  thf('6', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.78        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.58/0.78        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.78  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('8', plain,
% 0.58/0.78      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.58/0.78        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7'])).
% 0.58/0.78  thf('9', plain,
% 0.58/0.78      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.58/0.78         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['3', '8'])).
% 0.58/0.78  thf('10', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(dt_k3_subset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.78       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.78  thf('11', plain,
% 0.58/0.78      (![X2 : $i, X3 : $i]:
% 0.58/0.78         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.58/0.78          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.58/0.78  thf('12', plain,
% 0.58/0.78      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.78  thf(d3_tops_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( v1_tops_1 @ B @ A ) <=>
% 0.58/0.78             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('13', plain,
% 0.58/0.78      (![X17 : $i, X18 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.58/0.78          | ~ (v1_tops_1 @ X17 @ X18)
% 0.58/0.78          | ((k2_pre_topc @ X18 @ X17) = (k2_struct_0 @ X18))
% 0.58/0.78          | ~ (l1_pre_topc @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.78        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.78            = (k2_struct_0 @ sk_A))
% 0.58/0.78        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.78  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('16', plain,
% 0.58/0.78      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.78          = (k2_struct_0 @ sk_A))
% 0.58/0.78        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['14', '15'])).
% 0.58/0.78  thf('17', plain,
% 0.58/0.78      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.78          = (k2_struct_0 @ sk_A)))
% 0.58/0.78         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['9', '16'])).
% 0.58/0.78  thf(d3_struct_0, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.58/0.78  thf('18', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(d1_tops_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( k1_tops_1 @ A @ B ) =
% 0.58/0.78             ( k3_subset_1 @
% 0.58/0.78               ( u1_struct_0 @ A ) @ 
% 0.58/0.78               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.58/0.78          | ((k1_tops_1 @ X16 @ X15)
% 0.58/0.78              = (k3_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.58/0.78                 (k2_pre_topc @ X16 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15))))
% 0.58/0.78          | ~ (l1_pre_topc @ X16))),
% 0.58/0.78      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.78        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78               (k2_pre_topc @ sk_A @ 
% 0.58/0.78                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.78  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['18', '23'])).
% 0.58/0.78  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(dt_l1_pre_topc, axiom,
% 0.58/0.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.58/0.78  thf('26', plain,
% 0.58/0.78      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.78  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['24', '27'])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.58/0.78         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['17', '28'])).
% 0.58/0.78  thf(t4_subset_1, axiom,
% 0.58/0.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.58/0.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.78  thf(involutiveness_k3_subset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.78       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i]:
% 0.58/0.78         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.58/0.78          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.58/0.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.58/0.78  thf('32', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.78  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.58/0.78  thf('33', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.58/0.78  thf(t22_subset_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.58/0.78  thf('34', plain,
% 0.58/0.78      (![X6 : $i]:
% 0.58/0.78         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.58/0.78  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.58/0.78  thf('35', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.78  thf('36', plain,
% 0.58/0.78      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.58/0.78      inference('demod', [status(thm)], ['34', '35'])).
% 0.58/0.78  thf('37', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['33', '36'])).
% 0.58/0.78  thf('38', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.78      inference('demod', [status(thm)], ['32', '37'])).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.78         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['29', '38'])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.58/0.78         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.58/0.78         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.58/0.78             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.78  thf('42', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.58/0.78       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.58/0.78       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('45', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['44', '45'])).
% 0.58/0.78  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('48', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['46', '47'])).
% 0.58/0.78  thf('49', plain,
% 0.58/0.78      (![X2 : $i, X3 : $i]:
% 0.58/0.78         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.58/0.78          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.58/0.78  thf('50', plain,
% 0.58/0.78      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('51', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('52', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('53', plain,
% 0.58/0.78      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.78  thf('54', plain,
% 0.58/0.78      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.58/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['52', '53'])).
% 0.58/0.78  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('56', plain,
% 0.58/0.78      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['54', '55'])).
% 0.58/0.78  thf(dt_k2_pre_topc, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( l1_pre_topc @ A ) & 
% 0.58/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.78       ( m1_subset_1 @
% 0.58/0.78         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.78  thf('57', plain,
% 0.58/0.78      (![X12 : $i, X13 : $i]:
% 0.58/0.78         (~ (l1_pre_topc @ X12)
% 0.58/0.78          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.58/0.78          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.58/0.78             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.58/0.78  thf('58', plain,
% 0.58/0.78      (((m1_subset_1 @ 
% 0.58/0.78         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.78        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.78  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('60', plain,
% 0.58/0.78      ((m1_subset_1 @ 
% 0.58/0.78        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['58', '59'])).
% 0.58/0.78  thf('61', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('62', plain,
% 0.58/0.78      ((m1_subset_1 @ 
% 0.58/0.78        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['58', '59'])).
% 0.58/0.78  thf('63', plain,
% 0.58/0.78      (((m1_subset_1 @ 
% 0.58/0.78         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.78         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['61', '62'])).
% 0.58/0.78  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('65', plain,
% 0.58/0.78      ((m1_subset_1 @ 
% 0.58/0.78        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['63', '64'])).
% 0.58/0.78  thf('66', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i]:
% 0.58/0.78         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.58/0.78          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.58/0.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.58/0.78  thf('67', plain,
% 0.58/0.78      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.58/0.78         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.78  thf('68', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('69', plain,
% 0.58/0.78      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['24', '27'])).
% 0.58/0.78  thf('70', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['68', '69'])).
% 0.58/0.78  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('72', plain,
% 0.58/0.78      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['70', '71'])).
% 0.58/0.78  thf('73', plain,
% 0.58/0.78      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.78         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.58/0.78      inference('demod', [status(thm)], ['67', '72'])).
% 0.58/0.78  thf('74', plain,
% 0.58/0.78      ((m1_subset_1 @ 
% 0.58/0.78        (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['60', '73'])).
% 0.58/0.78  thf('75', plain,
% 0.58/0.78      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 0.58/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['51', '74'])).
% 0.58/0.78  thf('76', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['33', '36'])).
% 0.58/0.78  thf('77', plain,
% 0.58/0.78      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['75', '76'])).
% 0.58/0.78  thf('78', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i]:
% 0.58/0.78         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.58/0.78          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.58/0.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.58/0.78  thf('79', plain,
% 0.58/0.78      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.58/0.78          = (k2_struct_0 @ sk_A)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['77', '78'])).
% 0.58/0.78  thf('80', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('81', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('82', plain,
% 0.58/0.78      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.58/0.78  thf('83', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['81', '82'])).
% 0.58/0.78  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('85', plain,
% 0.58/0.78      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['83', '84'])).
% 0.58/0.78  thf('86', plain,
% 0.58/0.78      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.78         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.58/0.78      inference('demod', [status(thm)], ['67', '72'])).
% 0.58/0.78  thf('87', plain,
% 0.58/0.78      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['85', '86'])).
% 0.58/0.78  thf('88', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78             (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['80', '87'])).
% 0.58/0.78  thf('89', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('90', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['33', '36'])).
% 0.58/0.78  thf('91', plain,
% 0.58/0.78      ((((k1_xboole_0)
% 0.58/0.78          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.58/0.78  thf('92', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['33', '36'])).
% 0.58/0.78  thf('93', plain,
% 0.58/0.78      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['79', '91', '92'])).
% 0.58/0.78  thf('94', plain,
% 0.58/0.78      (![X17 : $i, X18 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.58/0.78          | ((k2_pre_topc @ X18 @ X17) != (k2_struct_0 @ X18))
% 0.58/0.78          | (v1_tops_1 @ X17 @ X18)
% 0.58/0.78          | ~ (l1_pre_topc @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.58/0.78  thf('95', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.58/0.78           | ~ (l1_pre_topc @ sk_A)
% 0.58/0.78           | (v1_tops_1 @ X0 @ sk_A)
% 0.58/0.78           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['93', '94'])).
% 0.58/0.78  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('97', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.58/0.78           | (v1_tops_1 @ X0 @ sk_A)
% 0.58/0.78           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96'])).
% 0.58/0.78  thf('98', plain,
% 0.58/0.78      (((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.58/0.78           != (k2_struct_0 @ sk_A))
% 0.58/0.78         | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['50', '97'])).
% 0.58/0.78  thf('99', plain,
% 0.58/0.78      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.78         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.58/0.78      inference('demod', [status(thm)], ['67', '72'])).
% 0.58/0.78  thf('100', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('101', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['33', '36'])).
% 0.58/0.78  thf('102', plain,
% 0.58/0.78      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.58/0.78         | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.58/0.78  thf('103', plain,
% 0.58/0.78      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('simplify', [status(thm)], ['102'])).
% 0.58/0.78  thf('104', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('105', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('106', plain,
% 0.58/0.78      (![X19 : $i, X20 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.58/0.78          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.58/0.78          | (v2_tops_1 @ X19 @ X20)
% 0.58/0.78          | ~ (l1_pre_topc @ X20))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.58/0.78  thf('107', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.78        | (v2_tops_1 @ sk_B @ sk_A)
% 0.58/0.78        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.78  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('109', plain,
% 0.58/0.78      (((v2_tops_1 @ sk_B @ sk_A)
% 0.58/0.78        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['107', '108'])).
% 0.58/0.78  thf('110', plain,
% 0.58/0.78      ((~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A)
% 0.58/0.78        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['104', '109'])).
% 0.58/0.78  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('112', plain,
% 0.58/0.78      ((~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.58/0.78        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['110', '111'])).
% 0.58/0.78  thf('113', plain,
% 0.58/0.78      (((v2_tops_1 @ sk_B @ sk_A))
% 0.58/0.78         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['103', '112'])).
% 0.58/0.78  thf('114', plain,
% 0.58/0.78      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('115', plain,
% 0.58/0.78      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.58/0.78       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['113', '114'])).
% 0.58/0.78  thf('116', plain, ($false),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '115'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
