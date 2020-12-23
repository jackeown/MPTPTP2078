%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1856+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jIJHZN0t5x

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 145 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 (1614 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(cc1_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_1])).

thf(t24_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) )
           => ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) )
              & ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) )
             => ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) )
                & ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tex_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('3',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('13',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X1 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('21',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','29'])).

thf('31',plain,
    ( ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
   <= ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( $false
   <= ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_1])).

thf('35',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
   <= ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('44',plain,(
    v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('46',plain,(
    ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['33','46'])).


%------------------------------------------------------------------------------
