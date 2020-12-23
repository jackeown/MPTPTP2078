%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TyphiVsVnk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:14 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 337 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   17
%              Number of atoms          : 1247 (3768 expanded)
%              Number of equality atoms :   41 (  72 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
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

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_tdlat_3 @ X22 )
      | ( v3_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('28',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32'])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['6','33'])).

thf('35',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v1_tops_1 @ X26 @ X27 )
      | ~ ( v3_tex_2 @ X26 @ X27 )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_tdlat_3 @ X22 )
      | ( v3_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','58'])).

thf('60',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('62',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('63',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('67',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('69',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('70',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('72',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('73',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_tex_2 @ X28 @ X29 )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ~ ( v1_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_tops_1 @ X0 @ sk_A )
        | ~ ( v2_tex_2 @ X0 @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_tops_1 @ X0 @ sk_A )
        | ~ ( v2_tex_2 @ X0 @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('89',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k7_subset_1 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('94',plain,
    ( ( ( sk_B_1
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('96',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ sk_B_1 @ X0 ) @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','96','97','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('102',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('103',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_tdlat_3 @ X22 )
      | ( v3_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v3_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( v3_pre_topc @ ( k4_xboole_0 @ sk_B_1 @ X0 ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','109'])).

thf('111',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','110'])).

thf('112',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('113',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_pre_topc @ X19 @ X18 )
       != ( u1_struct_0 @ X19 ) )
      | ( v1_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( sk_B_1
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('121',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','87','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('127',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','65','66','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TyphiVsVnk
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 214 iterations in 0.075s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.34/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.34/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.34/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.52  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.34/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.34/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.52  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.34/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.34/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.34/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.34/0.52  thf(t49_tex_2, conjecture,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.34/0.52         ( l1_pre_topc @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ( v3_tex_2 @ B @ A ) <=>
% 0.34/0.52             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]:
% 0.34/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.34/0.52            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.52          ( ![B:$i]:
% 0.34/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52              ( ( v3_tex_2 @ B @ A ) <=>
% 0.34/0.52                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.52        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.34/0.52       ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t52_pre_topc, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.34/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.34/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X15 : $i, X16 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.34/0.52          | ~ (v4_pre_topc @ X15 @ X16)
% 0.34/0.52          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 0.34/0.52          | ~ (l1_pre_topc @ X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.52        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.34/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.34/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t36_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.34/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.34/0.52  thf(t3_subset, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (![X8 : $i, X10 : $i]:
% 0.34/0.52         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.52  thf(d3_struct_0, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X11 : $i]:
% 0.34/0.52         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.52  thf(t17_tdlat_3, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.52       ( ( v1_tdlat_3 @ A ) <=>
% 0.34/0.52         ( ![B:$i]:
% 0.34/0.52           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X22 : $i, X23 : $i]:
% 0.34/0.52         (~ (v1_tdlat_3 @ X22)
% 0.34/0.52          | (v3_pre_topc @ X23 @ X22)
% 0.34/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.34/0.52          | ~ (l1_pre_topc @ X22)
% 0.34/0.52          | ~ (v2_pre_topc @ X22))),
% 0.34/0.52      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.34/0.52          | ~ (l1_struct_0 @ X0)
% 0.34/0.52          | ~ (v2_pre_topc @ X0)
% 0.34/0.52          | ~ (l1_pre_topc @ X0)
% 0.34/0.52          | (v3_pre_topc @ X1 @ X0)
% 0.34/0.52          | ~ (v1_tdlat_3 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_tdlat_3 @ X0)
% 0.34/0.52          | (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.34/0.52          | ~ (l1_pre_topc @ X0)
% 0.34/0.52          | ~ (v2_pre_topc @ X0)
% 0.34/0.52          | ~ (l1_struct_0 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['10', '13'])).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      (![X11 : $i]:
% 0.34/0.52         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.53  thf(d6_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.34/0.53             ( v3_pre_topc @
% 0.34/0.53               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.34/0.53               A ) ) ) ) ))).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.34/0.53          | ~ (v3_pre_topc @ 
% 0.34/0.53               (k7_subset_1 @ (u1_struct_0 @ X13) @ (k2_struct_0 @ X13) @ X12) @ 
% 0.34/0.53               X13)
% 0.34/0.53          | (v4_pre_topc @ X12 @ X13)
% 0.34/0.53          | ~ (l1_pre_topc @ X13))),
% 0.34/0.53      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (v3_pre_topc @ 
% 0.34/0.53             (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.34/0.53          | ~ (l1_struct_0 @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | (v4_pre_topc @ X1 @ X0)
% 0.34/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.53  thf(dt_k2_subset_1, axiom,
% 0.34/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.34/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.34/0.53  thf('19', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.53  thf('20', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.34/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.34/0.53          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.34/0.53          | ~ (l1_struct_0 @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | (v4_pre_topc @ X1 @ X0)
% 0.34/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.34/0.53      inference('demod', [status(thm)], ['17', '22'])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (l1_struct_0 @ X0)
% 0.34/0.53          | ~ (v2_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (v1_tdlat_3 @ X0)
% 0.34/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.34/0.53          | (v4_pre_topc @ X1 @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_struct_0 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['14', '23'])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((v4_pre_topc @ X1 @ X0)
% 0.34/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.34/0.53          | ~ (v1_tdlat_3 @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (v2_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_struct_0 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      ((~ (l1_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | ~ (v1_tdlat_3 @ sk_A)
% 0.34/0.53        | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '25'])).
% 0.34/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(dt_l1_pre_topc, axiom,
% 0.34/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.34/0.53  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('32', plain, ((v1_tdlat_3 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('33', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.34/0.53      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 0.34/0.53  thf('34', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.34/0.53      inference('demod', [status(thm)], ['6', '33'])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['35'])).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t47_tex_2, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.34/0.53             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (![X26 : $i, X27 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.34/0.53          | (v1_tops_1 @ X26 @ X27)
% 0.34/0.53          | ~ (v3_tex_2 @ X26 @ X27)
% 0.34/0.53          | ~ (v3_pre_topc @ X26 @ X27)
% 0.34/0.53          | ~ (l1_pre_topc @ X27)
% 0.34/0.53          | ~ (v2_pre_topc @ X27)
% 0.34/0.53          | (v2_struct_0 @ X27))),
% 0.34/0.53      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.34/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.34/0.53  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('42', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      (![X22 : $i, X23 : $i]:
% 0.34/0.53         (~ (v1_tdlat_3 @ X22)
% 0.34/0.53          | (v3_pre_topc @ X23 @ X22)
% 0.34/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.34/0.53          | ~ (l1_pre_topc @ X22)
% 0.34/0.53          | ~ (v2_pre_topc @ X22))),
% 0.34/0.53      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (v1_tdlat_3 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.34/0.53  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('47', plain, ((v1_tdlat_3 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('48', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.34/0.53      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.34/0.53  thf('49', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.34/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['39', '40', '41', '48'])).
% 0.34/0.53  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('51', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('clc', [status(thm)], ['49', '50'])).
% 0.34/0.53  thf('52', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['36', '51'])).
% 0.34/0.53  thf('53', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(d2_tops_3, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.34/0.53             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.34/0.53  thf('54', plain,
% 0.34/0.53      (![X18 : $i, X19 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.34/0.53          | ~ (v1_tops_1 @ X18 @ X19)
% 0.34/0.53          | ((k2_pre_topc @ X19 @ X18) = (u1_struct_0 @ X19))
% 0.34/0.53          | ~ (l1_pre_topc @ X19))),
% 0.34/0.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.34/0.53  thf('55', plain,
% 0.34/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.34/0.53  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('57', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.34/0.53  thf('58', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['52', '57'])).
% 0.34/0.53  thf('59', plain,
% 0.34/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['34', '58'])).
% 0.34/0.53  thf('60', plain,
% 0.34/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('61', plain,
% 0.34/0.53      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.34/0.53         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.34/0.53             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['59', '60'])).
% 0.34/0.53  thf(fc14_subset_1, axiom,
% 0.34/0.53    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.34/0.53  thf('62', plain, (![X7 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X7) @ X7)),
% 0.34/0.53      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.34/0.53  thf('63', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.53  thf('64', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 0.34/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.34/0.53  thf('65', plain,
% 0.34/0.53      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.34/0.53       ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['61', '64'])).
% 0.34/0.53  thf('66', plain,
% 0.34/0.53      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.34/0.53       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('split', [status(esa)], ['35'])).
% 0.34/0.53  thf('67', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.34/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('68', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(d7_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.34/0.53  thf('69', plain,
% 0.34/0.53      (![X20 : $i, X21 : $i]:
% 0.34/0.53         (((X21) = (X20))
% 0.34/0.53          | (v1_subset_1 @ X21 @ X20)
% 0.34/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.34/0.53  thf('70', plain,
% 0.34/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.34/0.53  thf('71', plain,
% 0.34/0.53      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('split', [status(esa)], ['35'])).
% 0.34/0.53  thf('72', plain,
% 0.34/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.53  thf(t48_tex_2, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.34/0.53             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.34/0.53  thf('73', plain,
% 0.34/0.53      (![X28 : $i, X29 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.34/0.53          | (v3_tex_2 @ X28 @ X29)
% 0.34/0.53          | ~ (v2_tex_2 @ X28 @ X29)
% 0.34/0.53          | ~ (v1_tops_1 @ X28 @ X29)
% 0.34/0.53          | ~ (l1_pre_topc @ X29)
% 0.34/0.53          | ~ (v2_pre_topc @ X29)
% 0.34/0.53          | (v2_struct_0 @ X29))),
% 0.34/0.53      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.34/0.53  thf('74', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.34/0.53           | (v2_struct_0 @ sk_A)
% 0.34/0.53           | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53           | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53           | ~ (v1_tops_1 @ X0 @ sk_A)
% 0.34/0.53           | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.34/0.53           | (v3_tex_2 @ X0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.34/0.53  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('77', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.34/0.53           | (v2_struct_0 @ sk_A)
% 0.34/0.53           | ~ (v1_tops_1 @ X0 @ sk_A)
% 0.34/0.53           | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.34/0.53           | (v3_tex_2 @ X0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.34/0.53  thf('78', plain,
% 0.34/0.53      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.34/0.53         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.34/0.53         | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.34/0.53         | (v2_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['67', '77'])).
% 0.34/0.53  thf('79', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t43_tex_2, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.34/0.53         ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.34/0.53  thf('80', plain,
% 0.34/0.53      (![X24 : $i, X25 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.34/0.53          | (v2_tex_2 @ X24 @ X25)
% 0.34/0.53          | ~ (l1_pre_topc @ X25)
% 0.34/0.53          | ~ (v1_tdlat_3 @ X25)
% 0.34/0.53          | ~ (v2_pre_topc @ X25)
% 0.34/0.53          | (v2_struct_0 @ X25))),
% 0.34/0.53      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.34/0.53  thf('81', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (v1_tdlat_3 @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.34/0.53  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('83', plain, ((v1_tdlat_3 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('85', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.34/0.53  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('87', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.34/0.53      inference('clc', [status(thm)], ['85', '86'])).
% 0.34/0.53  thf('88', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.34/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('89', plain,
% 0.34/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.53  thf('90', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.34/0.53          | ~ (v3_pre_topc @ 
% 0.34/0.53               (k7_subset_1 @ (u1_struct_0 @ X13) @ (k2_struct_0 @ X13) @ X12) @ 
% 0.34/0.53               X13)
% 0.34/0.53          | (v4_pre_topc @ X12 @ X13)
% 0.34/0.53          | ~ (l1_pre_topc @ X13))),
% 0.34/0.53      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.34/0.53  thf('91', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          (~ (v3_pre_topc @ 
% 0.34/0.53              (k7_subset_1 @ sk_B_1 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 0.34/0.53           | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53           | (v4_pre_topc @ X0 @ sk_A)
% 0.34/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.34/0.53  thf('92', plain,
% 0.34/0.53      (![X11 : $i]:
% 0.34/0.53         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.53  thf('93', plain,
% 0.34/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.53  thf('94', plain,
% 0.34/0.53      (((((sk_B_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['92', '93'])).
% 0.34/0.53  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('96', plain,
% 0.34/0.53      ((((sk_B_1) = (k2_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['94', '95'])).
% 0.34/0.53  thf('97', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('99', plain,
% 0.34/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.53  thf('100', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          (~ (v3_pre_topc @ (k4_xboole_0 @ sk_B_1 @ X0) @ sk_A)
% 0.34/0.53           | (v4_pre_topc @ X0 @ sk_A)
% 0.34/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['91', '96', '97', '98', '99'])).
% 0.34/0.53  thf('101', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.53  thf('102', plain,
% 0.34/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.53  thf('103', plain,
% 0.34/0.53      (![X22 : $i, X23 : $i]:
% 0.34/0.53         (~ (v1_tdlat_3 @ X22)
% 0.34/0.53          | (v3_pre_topc @ X23 @ X22)
% 0.34/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.34/0.53          | ~ (l1_pre_topc @ X22)
% 0.34/0.53          | ~ (v2_pre_topc @ X22))),
% 0.34/0.53      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.34/0.53  thf('104', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.34/0.53           | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53           | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53           | (v3_pre_topc @ X0 @ sk_A)
% 0.34/0.53           | ~ (v1_tdlat_3 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['102', '103'])).
% 0.34/0.53  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('107', plain, ((v1_tdlat_3 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('108', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.34/0.53           | (v3_pre_topc @ X0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.34/0.53  thf('109', plain,
% 0.34/0.53      ((![X0 : $i]: (v3_pre_topc @ (k4_xboole_0 @ sk_B_1 @ X0) @ sk_A))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['101', '108'])).
% 0.34/0.53  thf('110', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          ((v4_pre_topc @ X0 @ sk_A)
% 0.34/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['100', '109'])).
% 0.34/0.53  thf('111', plain,
% 0.34/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['88', '110'])).
% 0.34/0.53  thf('112', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.34/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.34/0.53  thf('113', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['111', '112'])).
% 0.34/0.53  thf('114', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('115', plain,
% 0.34/0.53      (![X18 : $i, X19 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.34/0.53          | ((k2_pre_topc @ X19 @ X18) != (u1_struct_0 @ X19))
% 0.34/0.53          | (v1_tops_1 @ X18 @ X19)
% 0.34/0.53          | ~ (l1_pre_topc @ X19))),
% 0.34/0.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.34/0.53  thf('116', plain,
% 0.34/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.34/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) != (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['114', '115'])).
% 0.34/0.53  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('118', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.34/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) != (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['116', '117'])).
% 0.34/0.53  thf('119', plain,
% 0.34/0.53      (((((sk_B_1) != (u1_struct_0 @ sk_A)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['113', '118'])).
% 0.34/0.53  thf('120', plain,
% 0.34/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.53  thf('121', plain,
% 0.34/0.53      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['119', '120'])).
% 0.34/0.53  thf('122', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('simplify', [status(thm)], ['121'])).
% 0.34/0.53  thf('123', plain,
% 0.34/0.53      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['78', '87', '122'])).
% 0.34/0.53  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('125', plain,
% 0.34/0.53      (((v3_tex_2 @ sk_B_1 @ sk_A))
% 0.34/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('clc', [status(thm)], ['123', '124'])).
% 0.34/0.53  thf('126', plain,
% 0.34/0.53      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('127', plain,
% 0.34/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.34/0.53       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['125', '126'])).
% 0.34/0.53  thf('128', plain, ($false),
% 0.34/0.53      inference('sat_resolution*', [status(thm)], ['1', '65', '66', '127'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.38/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
