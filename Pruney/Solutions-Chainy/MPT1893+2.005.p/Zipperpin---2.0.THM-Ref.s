%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OSR3TWcaha

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 808 expanded)
%              Number of leaves         :   37 ( 240 expanded)
%              Depth                    :   16
%              Number of atoms          :  901 (11783 expanded)
%              Number of equality atoms :   39 ( 153 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_tdlat_3 @ X24 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('4',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
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
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v1_tops_1 @ X26 @ X27 )
      | ~ ( v3_tex_2 @ X26 @ X27 )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_subset_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['38','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_B_2 @ sk_B_2 ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k4_xboole_0 @ sk_B_2 @ sk_B_2 ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k3_subset_1 @ sk_B_2 @ sk_B_2 )
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('61',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k3_subset_1 @ sk_B_2 @ sk_B_2 ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('68',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_tdlat_3 @ X22 )
      | ~ ( v3_pre_topc @ X23 @ X22 )
      | ( v4_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('74',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('81',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['38','43'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_B_2 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','81'])).

thf('86',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('87',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k4_xboole_0 @ sk_B_2 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','81'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('90',plain,
    ( ( ( k3_subset_1 @ sk_B_2 @ sk_B_2 )
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( k3_subset_1 @ sk_B_2 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['84','92'])).

thf('94',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( k3_subset_1 @ sk_B_2 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['65','95'])).

thf('97',plain,
    ( $false
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['45','96'])).

thf('98',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('99',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OSR3TWcaha
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 137 iterations in 0.059s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.50  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(t61_tex_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.50                ( v3_tex_2 @ B @ A ) & 
% 0.20/0.50                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.50                   ( v3_tex_2 @ B @ A ) & 
% 0.20/0.50                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t24_tdlat_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         (~ (v3_tdlat_3 @ X24)
% 0.20/0.50          | ~ (v4_pre_topc @ X25 @ X24)
% 0.20/0.50          | (v3_pre_topc @ X25 @ X24)
% 0.20/0.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.50          | ~ (l1_pre_topc @ X24)
% 0.20/0.50          | ~ (v2_pre_topc @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t47_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.20/0.50             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.50          | (v1_tops_1 @ X26 @ X27)
% 0.20/0.50          | ~ (v3_tex_2 @ X26 @ X27)
% 0.20/0.50          | ~ (v3_pre_topc @ X26 @ X27)
% 0.20/0.50          | ~ (l1_pre_topc @ X27)
% 0.20/0.50          | ~ (v2_pre_topc @ X27)
% 0.20/0.50          | (v2_struct_0 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.50        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.50  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d2_tops_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.50          | ~ (v1_tops_1 @ X18 @ X19)
% 0.20/0.50          | ((k2_pre_topc @ X19 @ X18) = (u1_struct_0 @ X19))
% 0.20/0.50          | ~ (l1_pre_topc @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t52_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.50             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.50               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50          | ~ (v4_pre_topc @ X16 @ X17)
% 0.20/0.50          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.20/0.50          | ~ (l1_pre_topc @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['25', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fc1_tex_2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X20)
% 0.20/0.50          | ~ (v1_subset_1 @ X21 @ X20)
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.20/0.50          | ~ (v1_xboole_0 @ (k3_subset_1 @ X20 @ X21)))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.20/0.50        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc4_subset_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.20/0.50          | ~ (v1_subset_1 @ X12 @ X13)
% 0.20/0.50          | ~ (v1_xboole_0 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))),
% 0.20/0.50      inference('clc', [status(thm)], ['38', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ (k3_subset_1 @ sk_B_2 @ sk_B_2)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['25', '32'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d5_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)
% 0.20/0.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)
% 0.20/0.50          = (k4_xboole_0 @ sk_B_2 @ sk_B_2)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['46', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['25', '32'])).
% 0.20/0.50  thf(t3_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('52', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.50  thf(t48_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.20/0.50           = (k3_xboole_0 @ X5 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['52', '53'])).
% 0.20/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((k3_subset_1 @ sk_B_2 @ sk_B_2) = (k3_xboole_0 @ k1_xboole_0 @ sk_B_2)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['50', '51', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.20/0.50           = (k3_xboole_0 @ X5 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf(t36_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.20/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.20/0.50      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.50  thf('61', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.50  thf(t69_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.50       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.50          | ~ (r1_tarski @ X8 @ X9)
% 0.20/0.50          | (v1_xboole_0 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k3_subset_1 @ sk_B_2 @ sk_B_2)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['57', '64'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t23_tdlat_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (v3_tdlat_3 @ X22)
% 0.20/0.50          | ~ (v3_pre_topc @ X23 @ X22)
% 0.20/0.50          | (v4_pre_topc @ X23 @ X22)
% 0.20/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.50          | ~ (l1_pre_topc @ X22)
% 0.20/0.50          | ~ (v2_pre_topc @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.50  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('77', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '78'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['70', '81'])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      (~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))),
% 0.20/0.50      inference('clc', [status(thm)], ['38', '43'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ (k3_subset_1 @ sk_B_2 @ sk_B_2)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['70', '81'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)
% 0.20/0.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)
% 0.20/0.50          = (k4_xboole_0 @ sk_B_2 @ sk_B_2)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['85', '86'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['70', '81'])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      ((((k3_subset_1 @ sk_B_2 @ sk_B_2) = (k3_xboole_0 @ k1_xboole_0 @ sk_B_2)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '63'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k3_subset_1 @ sk_B_2 @ sk_B_2)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['90', '91'])).
% 0.20/0.50  thf('93', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['84', '92'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('95', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 0.20/0.50  thf('96', plain, ((v1_xboole_0 @ (k3_subset_1 @ sk_B_2 @ sk_B_2))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['65', '95'])).
% 0.20/0.50  thf('97', plain, (($false) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['45', '96'])).
% 0.20/0.50  thf('98', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 0.20/0.50  thf('99', plain, ($false),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
