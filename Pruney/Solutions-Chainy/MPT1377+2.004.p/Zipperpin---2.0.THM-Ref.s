%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gFeIpRR8Xw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:44 EST 2020

% Result     : Theorem 17.69s
% Output     : Refutation 17.69s
% Verified   : 
% Statistics : Number of formulae       :  192 (1277 expanded)
%              Number of leaves         :   31 ( 365 expanded)
%              Depth                    :   18
%              Number of atoms          : 2507 (20309 expanded)
%              Number of equality atoms :   39 ( 285 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t33_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_compts_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_compts_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
          <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_compts_1])).

thf('0',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ~ ( v1_pre_topc @ X8 )
      | ( X8
        = ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('8',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( g1_pre_topc @ X18 @ X19 )
       != ( g1_pre_topc @ X16 @ X17 ) )
      | ( X18 = X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('29',plain,
    ( ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_pre_topc @ X26 @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('33',plain,
    ( ( ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','38','39'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X2 @ X1 )
        = X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('45',plain,(
    ! [X2: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) )
      | ( ( k8_setfam_1 @ X2 @ k1_xboole_0 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( k8_setfam_1 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','47'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X21 @ X20 ) )
        = X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('54',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','38','39'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('66',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf(t28_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_compts_1 @ C @ A )
                    <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_compts_1 @ X30 @ X28 )
      | ( v2_compts_1 @ X29 @ X27 )
      | ( X30 != X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_compts_1])).

thf('70',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_compts_1 @ X29 @ X27 )
      | ~ ( v2_compts_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_B @ X0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_B @ X0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) )
   <= ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X21 @ X20 ) )
        = X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('79',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('83',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['76','81','82'])).

thf('84',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('86',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_compts_1 @ X29 @ X27 )
      | ( v2_compts_1 @ X30 @ X28 )
      | ( X30 != X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_compts_1])).

thf('87',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_compts_1 @ X29 @ X28 )
      | ~ ( v2_compts_1 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ sk_A )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('93',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('94',plain,
    ( ( ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['3','24','62','63','97'])).

thf('99',plain,(
    ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('101',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('102',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('103',plain,
    ( ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['3','24','62'])).

thf('108',plain,(
    m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('110',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('111',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_compts_1 @ X29 @ X28 )
      | ~ ( v2_compts_1 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['3','24','62'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) ) )
    | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('120',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('121',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X21 @ X20 ) )
        = X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('122',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['3','24','62'])).

thf('127',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('129',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('130',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('131',plain,
    ( ( ~ ( l1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ~ ( l1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('135',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('136',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('137',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( l1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['133','140'])).

thf('142',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('143',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('144',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('145',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_compts_1 @ X29 @ X27 )
      | ~ ( v2_compts_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ sk_A )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ sk_A )
        | ( v2_compts_1 @ sk_B @ X0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('152',plain,
    ( ( ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['141','152'])).

thf('154',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf('155',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','24','62','63','97','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['3','24','62'])).

thf('157',plain,(
    v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['153','155','156'])).

thf('158',plain,(
    v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','127','128','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['99','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gFeIpRR8Xw
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.69/17.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.69/17.92  % Solved by: fo/fo7.sh
% 17.69/17.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.69/17.92  % done 9652 iterations in 17.479s
% 17.69/17.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.69/17.92  % SZS output start Refutation
% 17.69/17.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.69/17.92  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 17.69/17.92  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 17.69/17.92  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 17.69/17.92  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 17.69/17.92  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 17.69/17.92  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 17.69/17.92  thf(sk_A_type, type, sk_A: $i).
% 17.69/17.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.69/17.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.69/17.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.69/17.92  thf(sk_B_type, type, sk_B: $i).
% 17.69/17.92  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 17.69/17.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 17.69/17.92  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 17.69/17.92  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 17.69/17.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.69/17.92  thf(t33_compts_1, conjecture,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.69/17.92       ( ![B:$i]:
% 17.69/17.92         ( ( ( v2_compts_1 @ B @ A ) & 
% 17.69/17.92             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 17.69/17.92           ( ( v2_compts_1 @
% 17.69/17.92               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 17.69/17.92             ( m1_subset_1 @
% 17.69/17.92               B @ 
% 17.69/17.92               ( k1_zfmisc_1 @
% 17.69/17.92                 ( u1_struct_0 @
% 17.69/17.92                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 17.69/17.92  thf(zf_stmt_0, negated_conjecture,
% 17.69/17.92    (~( ![A:$i]:
% 17.69/17.92        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 17.69/17.92            ( l1_pre_topc @ A ) ) =>
% 17.69/17.92          ( ![B:$i]:
% 17.69/17.92            ( ( ( v2_compts_1 @ B @ A ) & 
% 17.69/17.92                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 17.69/17.92              ( ( v2_compts_1 @
% 17.69/17.92                  B @ 
% 17.69/17.92                  ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 17.69/17.92                ( m1_subset_1 @
% 17.69/17.92                  B @ 
% 17.69/17.92                  ( k1_zfmisc_1 @
% 17.69/17.92                    ( u1_struct_0 @
% 17.69/17.92                      ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )),
% 17.69/17.92    inference('cnf.neg', [status(esa)], [t33_compts_1])).
% 17.69/17.92  thf('0', plain,
% 17.69/17.92      ((~ (m1_subset_1 @ sk_B @ 
% 17.69/17.92           (k1_zfmisc_1 @ 
% 17.69/17.92            (u1_struct_0 @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92        | ~ (v2_compts_1 @ sk_B @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.69/17.92        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('1', plain,
% 17.69/17.92      ((~ (v2_compts_1 @ sk_B @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 17.69/17.92         <= (~
% 17.69/17.92             ((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 17.69/17.92      inference('split', [status(esa)], ['0'])).
% 17.69/17.92  thf('2', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('3', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))) | 
% 17.69/17.92       ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.69/17.92      inference('split', [status(esa)], ['2'])).
% 17.69/17.92  thf(dt_u1_pre_topc, axiom,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( l1_pre_topc @ A ) =>
% 17.69/17.92       ( m1_subset_1 @
% 17.69/17.92         ( u1_pre_topc @ A ) @ 
% 17.69/17.92         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 17.69/17.92  thf('4', plain,
% 17.69/17.92      (![X15 : $i]:
% 17.69/17.92         ((m1_subset_1 @ (u1_pre_topc @ X15) @ 
% 17.69/17.92           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 17.69/17.92          | ~ (l1_pre_topc @ X15))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 17.69/17.92  thf(dt_g1_pre_topc, axiom,
% 17.69/17.92    (![A:$i,B:$i]:
% 17.69/17.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 17.69/17.92       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 17.69/17.92         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 17.69/17.92  thf('5', plain,
% 17.69/17.92      (![X9 : $i, X10 : $i]:
% 17.69/17.92         ((v1_pre_topc @ (g1_pre_topc @ X9 @ X10))
% 17.69/17.92          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 17.69/17.92  thf('6', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (v1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['4', '5'])).
% 17.69/17.92  thf(abstractness_v1_pre_topc, axiom,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( l1_pre_topc @ A ) =>
% 17.69/17.92       ( ( v1_pre_topc @ A ) =>
% 17.69/17.92         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 17.69/17.92  thf('7', plain,
% 17.69/17.92      (![X8 : $i]:
% 17.69/17.92         (~ (v1_pre_topc @ X8)
% 17.69/17.92          | ((X8) = (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 17.69/17.92          | ~ (l1_pre_topc @ X8))),
% 17.69/17.92      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 17.69/17.92  thf('8', plain,
% 17.69/17.92      (![X15 : $i]:
% 17.69/17.92         ((m1_subset_1 @ (u1_pre_topc @ X15) @ 
% 17.69/17.92           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 17.69/17.92          | ~ (l1_pre_topc @ X15))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 17.69/17.92  thf(free_g1_pre_topc, axiom,
% 17.69/17.92    (![A:$i,B:$i]:
% 17.69/17.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 17.69/17.92       ( ![C:$i,D:$i]:
% 17.69/17.92         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 17.69/17.92           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 17.69/17.92  thf('9', plain,
% 17.69/17.92      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 17.69/17.92         (((g1_pre_topc @ X18 @ X19) != (g1_pre_topc @ X16 @ X17))
% 17.69/17.92          | ((X18) = (X16))
% 17.69/17.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 17.69/17.92      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 17.69/17.92  thf('10', plain,
% 17.69/17.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | ((u1_struct_0 @ X0) = (X1))
% 17.69/17.92          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 17.69/17.92              != (g1_pre_topc @ X1 @ X2)))),
% 17.69/17.92      inference('sup-', [status(thm)], ['8', '9'])).
% 17.69/17.92  thf('11', plain,
% 17.69/17.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.69/17.92         (((X0) != (g1_pre_topc @ X2 @ X1))
% 17.69/17.92          | ~ (l1_pre_topc @ X0)
% 17.69/17.92          | ~ (v1_pre_topc @ X0)
% 17.69/17.92          | ((u1_struct_0 @ X0) = (X2))
% 17.69/17.92          | ~ (l1_pre_topc @ X0))),
% 17.69/17.92      inference('sup-', [status(thm)], ['7', '10'])).
% 17.69/17.92  thf('12', plain,
% 17.69/17.92      (![X1 : $i, X2 : $i]:
% 17.69/17.92         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 17.69/17.92          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 17.69/17.92          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 17.69/17.92      inference('simplify', [status(thm)], ['11'])).
% 17.69/17.92  thf('13', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | ~ (l1_pre_topc @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 17.69/17.92          | ((u1_struct_0 @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 17.69/17.92              = (u1_struct_0 @ X0)))),
% 17.69/17.92      inference('sup-', [status(thm)], ['6', '12'])).
% 17.69/17.92  thf('14', plain,
% 17.69/17.92      (![X15 : $i]:
% 17.69/17.92         ((m1_subset_1 @ (u1_pre_topc @ X15) @ 
% 17.69/17.92           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 17.69/17.92          | ~ (l1_pre_topc @ X15))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 17.69/17.92  thf('15', plain,
% 17.69/17.92      (![X9 : $i, X10 : $i]:
% 17.69/17.92         ((l1_pre_topc @ (g1_pre_topc @ X9 @ X10))
% 17.69/17.92          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 17.69/17.92  thf('16', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (l1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['14', '15'])).
% 17.69/17.92  thf('17', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (((u1_struct_0 @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 17.69/17.92            = (u1_struct_0 @ X0))
% 17.69/17.92          | ~ (l1_pre_topc @ X0))),
% 17.69/17.92      inference('clc', [status(thm)], ['13', '16'])).
% 17.69/17.92  thf('18', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92        | (v2_compts_1 @ sk_B @ sk_A))),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('19', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('split', [status(esa)], ['18'])).
% 17.69/17.92  thf('20', plain,
% 17.69/17.92      ((((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.69/17.92         | ~ (l1_pre_topc @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup+', [status(thm)], ['17', '19'])).
% 17.69/17.92  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('22', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['20', '21'])).
% 17.69/17.92  thf('23', plain,
% 17.69/17.92      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.69/17.92         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('split', [status(esa)], ['0'])).
% 17.69/17.92  thf('24', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 17.69/17.92       ~
% 17.69/17.92       ((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['22', '23'])).
% 17.69/17.92  thf('25', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (l1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['14', '15'])).
% 17.69/17.92  thf('26', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('27', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('split', [status(esa)], ['26'])).
% 17.69/17.92  thf(dt_k1_pre_topc, axiom,
% 17.69/17.92    (![A:$i,B:$i]:
% 17.69/17.92     ( ( ( l1_pre_topc @ A ) & 
% 17.69/17.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.69/17.92       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 17.69/17.92         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 17.69/17.92  thf('28', plain,
% 17.69/17.92      (![X11 : $i, X12 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X11)
% 17.69/17.92          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 17.69/17.92          | (m1_pre_topc @ (k1_pre_topc @ X11 @ X12) @ X11))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 17.69/17.92  thf('29', plain,
% 17.69/17.92      ((((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 17.69/17.92         | ~ (l1_pre_topc @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['27', '28'])).
% 17.69/17.92  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('31', plain,
% 17.69/17.92      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['29', '30'])).
% 17.69/17.92  thf(t65_pre_topc, axiom,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( l1_pre_topc @ A ) =>
% 17.69/17.92       ( ![B:$i]:
% 17.69/17.92         ( ( l1_pre_topc @ B ) =>
% 17.69/17.92           ( ( m1_pre_topc @ A @ B ) <=>
% 17.69/17.92             ( m1_pre_topc @
% 17.69/17.92               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 17.69/17.92  thf('32', plain,
% 17.69/17.92      (![X25 : $i, X26 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X25)
% 17.69/17.92          | ~ (m1_pre_topc @ X26 @ X25)
% 17.69/17.92          | (m1_pre_topc @ X26 @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 17.69/17.92          | ~ (l1_pre_topc @ X26))),
% 17.69/17.92      inference('cnf', [status(esa)], [t65_pre_topc])).
% 17.69/17.92  thf('33', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 17.69/17.92         | (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92         | ~ (l1_pre_topc @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['31', '32'])).
% 17.69/17.92  thf('34', plain,
% 17.69/17.92      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['29', '30'])).
% 17.69/17.92  thf(dt_m1_pre_topc, axiom,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( l1_pre_topc @ A ) =>
% 17.69/17.92       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 17.69/17.92  thf('35', plain,
% 17.69/17.92      (![X13 : $i, X14 : $i]:
% 17.69/17.92         (~ (m1_pre_topc @ X13 @ X14)
% 17.69/17.92          | (l1_pre_topc @ X13)
% 17.69/17.92          | ~ (l1_pre_topc @ X14))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 17.69/17.92  thf('36', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['34', '35'])).
% 17.69/17.92  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('38', plain,
% 17.69/17.92      (((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['36', '37'])).
% 17.69/17.92  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('40', plain,
% 17.69/17.92      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['33', '38', '39'])).
% 17.69/17.92  thf(t4_subset_1, axiom,
% 17.69/17.92    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 17.69/17.92  thf('41', plain,
% 17.69/17.92      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 17.69/17.92  thf(dt_k8_setfam_1, axiom,
% 17.69/17.92    (![A:$i,B:$i]:
% 17.69/17.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 17.69/17.92       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 17.69/17.92  thf('42', plain,
% 17.69/17.92      (![X3 : $i, X4 : $i]:
% 17.69/17.92         ((m1_subset_1 @ (k8_setfam_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 17.69/17.92          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 17.69/17.92  thf('43', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('sup-', [status(thm)], ['41', '42'])).
% 17.69/17.92  thf(d10_setfam_1, axiom,
% 17.69/17.92    (![A:$i,B:$i]:
% 17.69/17.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 17.69/17.92       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 17.69/17.92           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 17.69/17.92         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 17.69/17.92  thf('44', plain,
% 17.69/17.92      (![X1 : $i, X2 : $i]:
% 17.69/17.92         (((X1) != (k1_xboole_0))
% 17.69/17.92          | ((k8_setfam_1 @ X2 @ X1) = (X2))
% 17.69/17.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2))))),
% 17.69/17.92      inference('cnf', [status(esa)], [d10_setfam_1])).
% 17.69/17.92  thf('45', plain,
% 17.69/17.92      (![X2 : $i]:
% 17.69/17.92         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2)))
% 17.69/17.92          | ((k8_setfam_1 @ X2 @ k1_xboole_0) = (X2)))),
% 17.69/17.92      inference('simplify', [status(thm)], ['44'])).
% 17.69/17.92  thf('46', plain,
% 17.69/17.92      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 17.69/17.92  thf('47', plain, (![X2 : $i]: ((k8_setfam_1 @ X2 @ k1_xboole_0) = (X2))),
% 17.69/17.92      inference('demod', [status(thm)], ['45', '46'])).
% 17.69/17.92  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('demod', [status(thm)], ['43', '47'])).
% 17.69/17.92  thf(t39_pre_topc, axiom,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( l1_pre_topc @ A ) =>
% 17.69/17.92       ( ![B:$i]:
% 17.69/17.92         ( ( m1_pre_topc @ B @ A ) =>
% 17.69/17.92           ( ![C:$i]:
% 17.69/17.92             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 17.69/17.92               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 17.69/17.92  thf('49', plain,
% 17.69/17.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.69/17.92         (~ (m1_pre_topc @ X22 @ X23)
% 17.69/17.92          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 17.69/17.92          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 17.69/17.92          | ~ (l1_pre_topc @ X23))),
% 17.69/17.92      inference('cnf', [status(esa)], [t39_pre_topc])).
% 17.69/17.92  thf('50', plain,
% 17.69/17.92      (![X0 : $i, X1 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X1)
% 17.69/17.92          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 17.69/17.92             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 17.69/17.92          | ~ (m1_pre_topc @ X0 @ X1))),
% 17.69/17.92      inference('sup-', [status(thm)], ['48', '49'])).
% 17.69/17.92  thf('51', plain,
% 17.69/17.92      ((((m1_subset_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 17.69/17.92          (k1_zfmisc_1 @ 
% 17.69/17.92           (u1_struct_0 @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         | ~ (l1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['40', '50'])).
% 17.69/17.92  thf('52', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('split', [status(esa)], ['26'])).
% 17.69/17.92  thf(t29_pre_topc, axiom,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( l1_pre_topc @ A ) =>
% 17.69/17.92       ( ![B:$i]:
% 17.69/17.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.69/17.92           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 17.69/17.92  thf('53', plain,
% 17.69/17.92      (![X20 : $i, X21 : $i]:
% 17.69/17.92         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 17.69/17.92          | ((u1_struct_0 @ (k1_pre_topc @ X21 @ X20)) = (X20))
% 17.69/17.92          | ~ (l1_pre_topc @ X21))),
% 17.69/17.92      inference('cnf', [status(esa)], [t29_pre_topc])).
% 17.69/17.92  thf('54', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ sk_A)
% 17.69/17.92         | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['52', '53'])).
% 17.69/17.92  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('56', plain,
% 17.69/17.92      ((((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['54', '55'])).
% 17.69/17.92  thf('57', plain,
% 17.69/17.92      ((((m1_subset_1 @ sk_B @ 
% 17.69/17.92          (k1_zfmisc_1 @ 
% 17.69/17.92           (u1_struct_0 @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         | ~ (l1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['51', '56'])).
% 17.69/17.92  thf('58', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ sk_A)
% 17.69/17.92         | (m1_subset_1 @ sk_B @ 
% 17.69/17.92            (k1_zfmisc_1 @ 
% 17.69/17.92             (u1_struct_0 @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['25', '57'])).
% 17.69/17.92  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('60', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['58', '59'])).
% 17.69/17.92  thf('61', plain,
% 17.69/17.92      ((~ (m1_subset_1 @ sk_B @ 
% 17.69/17.92           (k1_zfmisc_1 @ 
% 17.69/17.92            (u1_struct_0 @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 17.69/17.92         <= (~
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('split', [status(esa)], ['0'])).
% 17.69/17.92  thf('62', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))) | 
% 17.69/17.92       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['60', '61'])).
% 17.69/17.92  thf('63', plain,
% 17.69/17.92      (~
% 17.69/17.92       ((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 17.69/17.92       ~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 17.69/17.92       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 17.69/17.92       ~
% 17.69/17.92       ((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 17.69/17.92      inference('split', [status(esa)], ['0'])).
% 17.69/17.92  thf('64', plain,
% 17.69/17.92      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['33', '38', '39'])).
% 17.69/17.92  thf('65', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (l1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['14', '15'])).
% 17.69/17.92  thf('66', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92        | (v2_compts_1 @ sk_B @ sk_A))),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('67', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 17.69/17.92      inference('split', [status(esa)], ['66'])).
% 17.69/17.92  thf('68', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('split', [status(esa)], ['18'])).
% 17.69/17.92  thf(t28_compts_1, axiom,
% 17.69/17.92    (![A:$i]:
% 17.69/17.92     ( ( l1_pre_topc @ A ) =>
% 17.69/17.92       ( ![B:$i]:
% 17.69/17.92         ( ( m1_pre_topc @ B @ A ) =>
% 17.69/17.92           ( ![C:$i]:
% 17.69/17.92             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.69/17.92               ( ![D:$i]:
% 17.69/17.92                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 17.69/17.92                   ( ( ( C ) = ( D ) ) =>
% 17.69/17.92                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 17.69/17.92  thf('69', plain,
% 17.69/17.92      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 17.69/17.92         (~ (m1_pre_topc @ X27 @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 17.69/17.92          | ~ (v2_compts_1 @ X30 @ X28)
% 17.69/17.92          | (v2_compts_1 @ X29 @ X27)
% 17.69/17.92          | ((X30) != (X29))
% 17.69/17.92          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 17.69/17.92          | ~ (l1_pre_topc @ X28))),
% 17.69/17.92      inference('cnf', [status(esa)], [t28_compts_1])).
% 17.69/17.92  thf('70', plain,
% 17.69/17.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 17.69/17.92          | (v2_compts_1 @ X29 @ X27)
% 17.69/17.92          | ~ (v2_compts_1 @ X29 @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 17.69/17.92          | ~ (m1_pre_topc @ X27 @ X28))),
% 17.69/17.92      inference('simplify', [status(thm)], ['69'])).
% 17.69/17.92  thf('71', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (m1_pre_topc @ X0 @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ 
% 17.69/17.92                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | ~ (l1_pre_topc @ 
% 17.69/17.92                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['68', '70'])).
% 17.69/17.92  thf('72', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (l1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (m1_pre_topc @ X0 @ 
% 17.69/17.92                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['67', '71'])).
% 17.69/17.92  thf('73', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (l1_pre_topc @ sk_A)
% 17.69/17.92           | ~ (m1_pre_topc @ X0 @ 
% 17.69/17.92                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | (v2_compts_1 @ sk_B @ X0)))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['65', '72'])).
% 17.69/17.92  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('75', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (m1_pre_topc @ X0 @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | (v2_compts_1 @ sk_B @ X0)))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['73', '74'])).
% 17.69/17.92  thf('76', plain,
% 17.69/17.92      ((((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 17.69/17.92         | ~ (m1_subset_1 @ sk_B @ 
% 17.69/17.92              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 17.69/17.92             ((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['64', '75'])).
% 17.69/17.92  thf('77', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['20', '21'])).
% 17.69/17.92  thf('78', plain,
% 17.69/17.92      (![X20 : $i, X21 : $i]:
% 17.69/17.92         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 17.69/17.92          | ((u1_struct_0 @ (k1_pre_topc @ X21 @ X20)) = (X20))
% 17.69/17.92          | ~ (l1_pre_topc @ X21))),
% 17.69/17.92      inference('cnf', [status(esa)], [t29_pre_topc])).
% 17.69/17.92  thf('79', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ sk_A)
% 17.69/17.92         | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['77', '78'])).
% 17.69/17.92  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('81', plain,
% 17.69/17.92      ((((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['79', '80'])).
% 17.69/17.92  thf('82', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('demod', [status(thm)], ['43', '47'])).
% 17.69/17.92  thf('83', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 17.69/17.92             ((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['76', '81', '82'])).
% 17.69/17.92  thf('84', plain,
% 17.69/17.92      ((((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['54', '55'])).
% 17.69/17.92  thf('85', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('split', [status(esa)], ['26'])).
% 17.69/17.92  thf('86', plain,
% 17.69/17.92      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 17.69/17.92         (~ (m1_pre_topc @ X27 @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 17.69/17.92          | ~ (v2_compts_1 @ X29 @ X27)
% 17.69/17.92          | (v2_compts_1 @ X30 @ X28)
% 17.69/17.92          | ((X30) != (X29))
% 17.69/17.92          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 17.69/17.92          | ~ (l1_pre_topc @ X28))),
% 17.69/17.92      inference('cnf', [status(esa)], [t28_compts_1])).
% 17.69/17.92  thf('87', plain,
% 17.69/17.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 17.69/17.92          | (v2_compts_1 @ X29 @ X28)
% 17.69/17.92          | ~ (v2_compts_1 @ X29 @ X27)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 17.69/17.92          | ~ (m1_pre_topc @ X27 @ X28))),
% 17.69/17.92      inference('simplify', [status(thm)], ['86'])).
% 17.69/17.92  thf('88', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (m1_pre_topc @ X0 @ sk_A)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | (v2_compts_1 @ sk_B @ sk_A)
% 17.69/17.92           | ~ (l1_pre_topc @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['85', '87'])).
% 17.69/17.92  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('90', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (m1_pre_topc @ X0 @ sk_A)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | (v2_compts_1 @ sk_B @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['88', '89'])).
% 17.69/17.92  thf('91', plain,
% 17.69/17.92      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 17.69/17.92         | (v2_compts_1 @ sk_B @ sk_A)
% 17.69/17.92         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 17.69/17.92         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['84', '90'])).
% 17.69/17.92  thf('92', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('demod', [status(thm)], ['43', '47'])).
% 17.69/17.92  thf('93', plain,
% 17.69/17.92      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['29', '30'])).
% 17.69/17.92  thf('94', plain,
% 17.69/17.92      ((((v2_compts_1 @ sk_B @ sk_A)
% 17.69/17.92         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.69/17.92      inference('demod', [status(thm)], ['91', '92', '93'])).
% 17.69/17.92  thf('95', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ sk_A))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 17.69/17.92             ((v2_compts_1 @ sk_B @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['83', '94'])).
% 17.69/17.92  thf('96', plain,
% 17.69/17.92      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 17.69/17.92      inference('split', [status(esa)], ['0'])).
% 17.69/17.92  thf('97', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 17.69/17.92       ~
% 17.69/17.92       ((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 17.69/17.92       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 17.69/17.92       ~
% 17.69/17.92       ((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['95', '96'])).
% 17.69/17.92  thf('98', plain,
% 17.69/17.92      (~
% 17.69/17.92       ((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 17.69/17.92      inference('sat_resolution*', [status(thm)], ['3', '24', '62', '63', '97'])).
% 17.69/17.92  thf('99', plain,
% 17.69/17.92      (~ (v2_compts_1 @ sk_B @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 17.69/17.92      inference('simpl_trail', [status(thm)], ['1', '98'])).
% 17.69/17.92  thf('100', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (l1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['14', '15'])).
% 17.69/17.92  thf('101', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('split', [status(esa)], ['18'])).
% 17.69/17.92  thf('102', plain,
% 17.69/17.92      (![X11 : $i, X12 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X11)
% 17.69/17.92          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 17.69/17.92          | (m1_pre_topc @ (k1_pre_topc @ X11 @ X12) @ X11))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 17.69/17.92  thf('103', plain,
% 17.69/17.92      ((((m1_pre_topc @ 
% 17.69/17.92          (k1_pre_topc @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92         | ~ (l1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['101', '102'])).
% 17.69/17.92  thf('104', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ sk_A)
% 17.69/17.92         | (m1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['100', '103'])).
% 17.69/17.92  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('106', plain,
% 17.69/17.92      (((m1_pre_topc @ 
% 17.69/17.92         (k1_pre_topc @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['104', '105'])).
% 17.69/17.92  thf('107', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 17.69/17.92      inference('sat_resolution*', [status(thm)], ['3', '24', '62'])).
% 17.69/17.92  thf('108', plain,
% 17.69/17.92      ((m1_pre_topc @ 
% 17.69/17.92        (k1_pre_topc @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 17.69/17.92      inference('simpl_trail', [status(thm)], ['106', '107'])).
% 17.69/17.92  thf('109', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (l1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['14', '15'])).
% 17.69/17.92  thf('110', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('split', [status(esa)], ['18'])).
% 17.69/17.92  thf('111', plain,
% 17.69/17.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 17.69/17.92          | (v2_compts_1 @ X29 @ X28)
% 17.69/17.92          | ~ (v2_compts_1 @ X29 @ X27)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 17.69/17.92          | ~ (m1_pre_topc @ X27 @ X28))),
% 17.69/17.92      inference('simplify', [status(thm)], ['86'])).
% 17.69/17.92  thf('112', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (m1_pre_topc @ X0 @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | (v2_compts_1 @ sk_B @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | ~ (l1_pre_topc @ 
% 17.69/17.92                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['110', '111'])).
% 17.69/17.92  thf('113', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (l1_pre_topc @ sk_A)
% 17.69/17.92           | (v2_compts_1 @ sk_B @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (m1_pre_topc @ X0 @ 
% 17.69/17.92                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['109', '112'])).
% 17.69/17.92  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('115', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          ((v2_compts_1 @ sk_B @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (m1_pre_topc @ X0 @ 
% 17.69/17.92                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['113', '114'])).
% 17.69/17.92  thf('116', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 17.69/17.92      inference('sat_resolution*', [status(thm)], ['3', '24', '62'])).
% 17.69/17.92  thf('117', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         ((v2_compts_1 @ sk_B @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92          | ~ (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92          | ~ (m1_pre_topc @ X0 @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 17.69/17.92      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 17.69/17.92  thf('118', plain,
% 17.69/17.92      ((~ (m1_subset_1 @ sk_B @ 
% 17.69/17.92           (k1_zfmisc_1 @ 
% 17.69/17.92            (u1_struct_0 @ 
% 17.69/17.92             (k1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 17.69/17.92              sk_B))))
% 17.69/17.92        | ~ (v2_compts_1 @ sk_B @ 
% 17.69/17.92             (k1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 17.69/17.92              sk_B))
% 17.69/17.92        | (v2_compts_1 @ sk_B @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['108', '117'])).
% 17.69/17.92  thf('119', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (l1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['14', '15'])).
% 17.69/17.92  thf('120', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('split', [status(esa)], ['18'])).
% 17.69/17.92  thf('121', plain,
% 17.69/17.92      (![X20 : $i, X21 : $i]:
% 17.69/17.92         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 17.69/17.92          | ((u1_struct_0 @ (k1_pre_topc @ X21 @ X20)) = (X20))
% 17.69/17.92          | ~ (l1_pre_topc @ X21))),
% 17.69/17.92      inference('cnf', [status(esa)], [t29_pre_topc])).
% 17.69/17.92  thf('122', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92         | ((u1_struct_0 @ 
% 17.69/17.92             (k1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 17.69/17.92              sk_B))
% 17.69/17.92             = (sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['120', '121'])).
% 17.69/17.92  thf('123', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ sk_A)
% 17.69/17.92         | ((u1_struct_0 @ 
% 17.69/17.92             (k1_pre_topc @ 
% 17.69/17.92              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 17.69/17.92              sk_B))
% 17.69/17.92             = (sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['119', '122'])).
% 17.69/17.92  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('125', plain,
% 17.69/17.92      ((((u1_struct_0 @ 
% 17.69/17.92          (k1_pre_topc @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 17.69/17.92          = (sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['123', '124'])).
% 17.69/17.92  thf('126', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 17.69/17.92      inference('sat_resolution*', [status(thm)], ['3', '24', '62'])).
% 17.69/17.92  thf('127', plain,
% 17.69/17.92      (((u1_struct_0 @ 
% 17.69/17.92         (k1_pre_topc @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 17.69/17.92         = (sk_B))),
% 17.69/17.92      inference('simpl_trail', [status(thm)], ['125', '126'])).
% 17.69/17.92  thf('128', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('demod', [status(thm)], ['43', '47'])).
% 17.69/17.92  thf('129', plain,
% 17.69/17.92      (((m1_pre_topc @ 
% 17.69/17.92         (k1_pre_topc @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['104', '105'])).
% 17.69/17.92  thf('130', plain,
% 17.69/17.92      (![X25 : $i, X26 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X25)
% 17.69/17.92          | ~ (m1_pre_topc @ X26 @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 17.69/17.92          | (m1_pre_topc @ X26 @ X25)
% 17.69/17.92          | ~ (l1_pre_topc @ X26))),
% 17.69/17.92      inference('cnf', [status(esa)], [t65_pre_topc])).
% 17.69/17.92  thf('131', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 17.69/17.92         | (m1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92            sk_A)
% 17.69/17.92         | ~ (l1_pre_topc @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['129', '130'])).
% 17.69/17.92  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('133', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 17.69/17.92         | (m1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92            sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['131', '132'])).
% 17.69/17.92  thf('134', plain,
% 17.69/17.92      (![X0 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X0)
% 17.69/17.92          | (l1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['14', '15'])).
% 17.69/17.92  thf('135', plain,
% 17.69/17.92      (((m1_pre_topc @ 
% 17.69/17.92         (k1_pre_topc @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['104', '105'])).
% 17.69/17.92  thf('136', plain,
% 17.69/17.92      (![X13 : $i, X14 : $i]:
% 17.69/17.92         (~ (m1_pre_topc @ X13 @ X14)
% 17.69/17.92          | (l1_pre_topc @ X13)
% 17.69/17.92          | ~ (l1_pre_topc @ X14))),
% 17.69/17.92      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 17.69/17.92  thf('137', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ 
% 17.69/17.92            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 17.69/17.92         | (l1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['135', '136'])).
% 17.69/17.92  thf('138', plain,
% 17.69/17.92      (((~ (l1_pre_topc @ sk_A)
% 17.69/17.92         | (l1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['134', '137'])).
% 17.69/17.92  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('140', plain,
% 17.69/17.92      (((l1_pre_topc @ 
% 17.69/17.92         (k1_pre_topc @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['138', '139'])).
% 17.69/17.92  thf('141', plain,
% 17.69/17.92      (((m1_pre_topc @ 
% 17.69/17.92         (k1_pre_topc @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92         sk_A))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['133', '140'])).
% 17.69/17.92  thf('142', plain,
% 17.69/17.92      ((((u1_struct_0 @ 
% 17.69/17.92          (k1_pre_topc @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 17.69/17.92          = (sk_B)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['123', '124'])).
% 17.69/17.92  thf('143', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 17.69/17.92      inference('split', [status(esa)], ['66'])).
% 17.69/17.92  thf('144', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['20', '21'])).
% 17.69/17.92  thf('145', plain,
% 17.69/17.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 17.69/17.92         (~ (l1_pre_topc @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 17.69/17.92          | (v2_compts_1 @ X29 @ X27)
% 17.69/17.92          | ~ (v2_compts_1 @ X29 @ X28)
% 17.69/17.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 17.69/17.92          | ~ (m1_pre_topc @ X27 @ X28))),
% 17.69/17.92      inference('simplify', [status(thm)], ['69'])).
% 17.69/17.92  thf('146', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (m1_pre_topc @ X0 @ sk_A)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ sk_A)
% 17.69/17.92           | (v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | ~ (l1_pre_topc @ sk_A)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['144', '145'])).
% 17.69/17.92  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 17.69/17.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.69/17.92  thf('148', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          (~ (m1_pre_topc @ X0 @ sk_A)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (v2_compts_1 @ sk_B @ sk_A)
% 17.69/17.92           | (v2_compts_1 @ sk_B @ X0)))
% 17.69/17.92         <= (((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['146', '147'])).
% 17.69/17.92  thf('149', plain,
% 17.69/17.92      ((![X0 : $i]:
% 17.69/17.92          ((v2_compts_1 @ sk_B @ X0)
% 17.69/17.92           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 17.69/17.92           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['143', '148'])).
% 17.69/17.92  thf('150', plain,
% 17.69/17.92      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 17.69/17.92         | ~ (m1_pre_topc @ 
% 17.69/17.92              (k1_pre_topc @ 
% 17.69/17.92               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 17.69/17.92               sk_B) @ 
% 17.69/17.92              sk_A)
% 17.69/17.92         | (v2_compts_1 @ sk_B @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['142', '149'])).
% 17.69/17.92  thf('151', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.69/17.92      inference('demod', [status(thm)], ['43', '47'])).
% 17.69/17.92  thf('152', plain,
% 17.69/17.92      (((~ (m1_pre_topc @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 17.69/17.92            sk_A)
% 17.69/17.92         | (v2_compts_1 @ sk_B @ 
% 17.69/17.92            (k1_pre_topc @ 
% 17.69/17.92             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('demod', [status(thm)], ['150', '151'])).
% 17.69/17.92  thf('153', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (k1_pre_topc @ 
% 17.69/17.92          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 17.69/17.92         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 17.69/17.92             ((m1_subset_1 @ sk_B @ 
% 17.69/17.92               (k1_zfmisc_1 @ 
% 17.69/17.92                (u1_struct_0 @ 
% 17.69/17.92                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 17.69/17.92      inference('sup-', [status(thm)], ['141', '152'])).
% 17.69/17.92  thf('154', plain,
% 17.69/17.92      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 17.69/17.92       ((v2_compts_1 @ sk_B @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 17.69/17.92      inference('split', [status(esa)], ['66'])).
% 17.69/17.92  thf('155', plain, (((v2_compts_1 @ sk_B @ sk_A))),
% 17.69/17.92      inference('sat_resolution*', [status(thm)],
% 17.69/17.92                ['3', '24', '62', '63', '97', '154'])).
% 17.69/17.92  thf('156', plain,
% 17.69/17.92      (((m1_subset_1 @ sk_B @ 
% 17.69/17.92         (k1_zfmisc_1 @ 
% 17.69/17.92          (u1_struct_0 @ 
% 17.69/17.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 17.69/17.92      inference('sat_resolution*', [status(thm)], ['3', '24', '62'])).
% 17.69/17.92  thf('157', plain,
% 17.69/17.92      ((v2_compts_1 @ sk_B @ 
% 17.69/17.92        (k1_pre_topc @ 
% 17.69/17.92         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 17.69/17.92      inference('simpl_trail', [status(thm)], ['153', '155', '156'])).
% 17.69/17.92  thf('158', plain,
% 17.69/17.92      ((v2_compts_1 @ sk_B @ 
% 17.69/17.92        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 17.69/17.92      inference('demod', [status(thm)], ['118', '127', '128', '157'])).
% 17.69/17.92  thf('159', plain, ($false), inference('demod', [status(thm)], ['99', '158'])).
% 17.69/17.92  
% 17.69/17.92  % SZS output end Refutation
% 17.69/17.92  
% 17.78/17.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
