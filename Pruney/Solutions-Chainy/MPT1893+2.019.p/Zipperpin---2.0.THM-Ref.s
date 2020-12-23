%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQBQN9dTjl

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:36 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 246 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  875 (3194 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(t61_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( ( v3_pre_topc @ B @ A )
                | ( v4_pre_topc @ B @ A ) )
              & ( v3_tex_2 @ B @ A )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( ( v3_pre_topc @ B @ A )
                  | ( v4_pre_topc @ B @ A ) )
                & ( v3_tex_2 @ B @ A )
                & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tex_2])).

thf('0',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v4_pre_topc @ X18 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('4',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_tops_1 @ X19 @ X20 )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_tops_1 @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('38',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['44','47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v4_pre_topc @ X18 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v3_tdlat_3 @ sk_A )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('76',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('79',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','79'])).

thf('81',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('83',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('84',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('85',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_subset_1 @ sk_B_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['35','88'])).

thf('90',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('91',plain,(
    $false ),
    inference('sup-',[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQBQN9dTjl
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:14:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 115 iterations in 0.070s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.36/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.36/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(t61_tex_2, conjecture,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.53         ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.36/0.53                ( v3_tex_2 @ B @ A ) & 
% 0.36/0.53                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i]:
% 0.36/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.53            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53          ( ![B:$i]:
% 0.36/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.36/0.53                   ( v3_tex_2 @ B @ A ) & 
% 0.36/0.53                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.36/0.53  thf('0', plain,
% 0.36/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t24_tdlat_3, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ( v3_tdlat_3 @ A ) <=>
% 0.36/0.53         ( ![B:$i]:
% 0.36/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      (![X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (v3_tdlat_3 @ X17)
% 0.36/0.53          | ~ (v4_pre_topc @ X18 @ X17)
% 0.36/0.53          | (v3_pre_topc @ X18 @ X17)
% 0.36/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.53          | ~ (l1_pre_topc @ X17)
% 0.36/0.53          | ~ (v2_pre_topc @ X17))),
% 0.36/0.53      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.53  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('7', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['1', '8'])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t47_tex_2, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.36/0.53             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      (![X19 : $i, X20 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.53          | (v1_tops_1 @ X19 @ X20)
% 0.36/0.53          | ~ (v3_tex_2 @ X19 @ X20)
% 0.36/0.53          | ~ (v3_pre_topc @ X19 @ X20)
% 0.36/0.53          | ~ (l1_pre_topc @ X20)
% 0.36/0.53          | ~ (v2_pre_topc @ X20)
% 0.36/0.53          | (v2_struct_0 @ X20))),
% 0.36/0.53      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (((v2_struct_0 @ sk_A)
% 0.36/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.53  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('15', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (((v2_struct_0 @ sk_A)
% 0.36/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.36/0.53  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['9', '18'])).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(d2_tops_3, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.36/0.53             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      (![X15 : $i, X16 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.53          | ~ (v1_tops_1 @ X15 @ X16)
% 0.36/0.53          | ((k2_pre_topc @ X16 @ X15) = (u1_struct_0 @ X16))
% 0.36/0.53          | ~ (l1_pre_topc @ X16))),
% 0.36/0.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.36/0.53  thf('22', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.53  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.36/0.53         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['19', '24'])).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('27', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t52_pre_topc, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.36/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.36/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.53  thf('28', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.36/0.53          | ~ (v4_pre_topc @ X11 @ X12)
% 0.36/0.53          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.36/0.53          | ~ (l1_pre_topc @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.36/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.53  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('31', plain,
% 0.36/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.36/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.36/0.53         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['26', '31'])).
% 0.36/0.53  thf('33', plain,
% 0.36/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['25', '32'])).
% 0.36/0.53  thf('34', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('35', plain,
% 0.36/0.53      (((v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.53  thf('36', plain,
% 0.36/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('37', plain,
% 0.36/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.53  thf('38', plain,
% 0.36/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.53  thf('39', plain,
% 0.36/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.36/0.53  thf('40', plain,
% 0.36/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.36/0.53         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.53  thf('41', plain,
% 0.36/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i]:
% 0.36/0.53         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.36/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.53  thf('45', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(d5_subset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      (![X3 : $i, X4 : $i]:
% 0.36/0.53         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.36/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.53  thf('47', plain,
% 0.36/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.36/0.53         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.36/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.53  thf(t36_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.36/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.53  thf(t3_subset, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      (![X8 : $i, X10 : $i]:
% 0.36/0.53         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      (![X3 : $i, X4 : $i]:
% 0.36/0.53         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.36/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.53           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.53  thf('53', plain,
% 0.36/0.53      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['44', '47', '52'])).
% 0.36/0.53  thf('54', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.53  thf(t29_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.53             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.54          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.36/0.54          | (v4_pre_topc @ X13 @ X14)
% 0.36/0.54          | ~ (l1_pre_topc @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X0)
% 0.36/0.54          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.54          | ~ (v3_pre_topc @ 
% 0.36/0.54               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.36/0.54                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.36/0.54               X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.54           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X0)
% 0.36/0.54          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.54          | ~ (v3_pre_topc @ 
% 0.36/0.54               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.36/0.54                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.36/0.54               X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['56', '57'])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.54        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['53', '58'])).
% 0.36/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('61', plain,
% 0.36/0.54      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.54        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.36/0.54         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['41', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i]:
% 0.36/0.54         (~ (v3_tdlat_3 @ X17)
% 0.36/0.54          | ~ (v4_pre_topc @ X18 @ X17)
% 0.36/0.54          | (v3_pre_topc @ X18 @ X17)
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.54          | ~ (l1_pre_topc @ X17)
% 0.36/0.54          | ~ (v2_pre_topc @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v2_pre_topc @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.54          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.54          | ~ (v3_tdlat_3 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      (((~ (v3_tdlat_3 @ sk_A)
% 0.36/0.54         | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.36/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54         | ~ (v2_pre_topc @ sk_A))) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['62', '65'])).
% 0.36/0.54  thf('67', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('70', plain,
% 0.36/0.54      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.36/0.54         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.36/0.54  thf('71', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('72', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.54          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.36/0.54          | (v4_pre_topc @ X13 @ X14)
% 0.36/0.54          | ~ (l1_pre_topc @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.36/0.54  thf('73', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.54        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.36/0.54  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('75', plain,
% 0.36/0.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.36/0.54         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.54        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['70', '76'])).
% 0.36/0.54  thf('78', plain,
% 0.36/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.36/0.54        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.54  thf('79', plain,
% 0.36/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.36/0.54         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.54  thf('80', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['40', '79'])).
% 0.36/0.54  thf('81', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('82', plain,
% 0.36/0.54      (((v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['80', '81'])).
% 0.36/0.54  thf(fc14_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.36/0.54  thf('83', plain, (![X7 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X7) @ X7)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.36/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.54  thf('84', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.54  thf('85', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 0.36/0.54      inference('demod', [status(thm)], ['83', '84'])).
% 0.36/0.54  thf('86', plain, (~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['82', '85'])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      (((v4_pre_topc @ sk_B_1 @ sk_A)) | ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('88', plain, (((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.36/0.54  thf('89', plain, ((v1_subset_1 @ sk_B_1 @ sk_B_1)),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['35', '88'])).
% 0.36/0.54  thf('90', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 0.36/0.54      inference('demod', [status(thm)], ['83', '84'])).
% 0.36/0.54  thf('91', plain, ($false), inference('sup-', [status(thm)], ['89', '90'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
