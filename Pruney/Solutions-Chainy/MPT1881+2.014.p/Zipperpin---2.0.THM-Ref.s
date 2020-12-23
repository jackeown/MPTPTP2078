%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iwJGs5K8Zo

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 611 expanded)
%              Number of leaves         :   39 ( 192 expanded)
%              Depth                    :   20
%              Number of atoms          : 1427 (6767 expanded)
%              Number of equality atoms :   56 ( 148 expanded)
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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('4',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_tex_2 @ X27 @ X28 )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v1_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
      | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('15',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
       != ( u1_struct_0 @ X18 ) )
      | ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k7_subset_1 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('30',plain,
    ( ( ( sk_B_1
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k7_subset_1 @ X7 @ X6 @ X8 )
        = ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ sk_B_1 @ X0 ) @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','34','37','38','39'])).

thf('41',plain,
    ( ( ~ ( v3_pre_topc @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( v4_pre_topc @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('43',plain,
    ( ( ~ ( v3_pre_topc @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ sk_A )
      | ( v4_pre_topc @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_tdlat_3 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v3_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','61'])).

thf('63',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('65',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','63','64','65','74','75','76'])).

thf('78',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('79',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_tops_1 @ X25 @ X26 )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_tdlat_3 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('87',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('102',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('106',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('108',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('118',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('121',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('125',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('128',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('130',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','130'])).

thf('132',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_tdlat_3 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('133',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['118','137'])).

thf('139',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['101','138'])).

thf('140',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['100','139'])).

thf('141',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','140'])).

thf('142',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('143',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('144',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('146',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ X9 @ X9 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['78','147'])).

thf('149',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['77','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,
    ( $false
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['1','151'])).

thf('153',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('154',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['78','147','153'])).

thf('155',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['152','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iwJGs5K8Zo
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 250 iterations in 0.124s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.58  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.58  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.58  thf(t49_tex_2, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.58         ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.58             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.58            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58          ( ![B:$i]:
% 0.20/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58              ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.58                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.58        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(d7_subset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X19 : $i, X20 : $i]:
% 0.20/0.58         (((X20) = (X19))
% 0.20/0.58          | (v1_subset_1 @ X20 @ X19)
% 0.20/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.58        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.58        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('split', [status(esa)], ['5'])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.58  thf(dt_k2_subset_1, axiom,
% 0.20/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.58  thf('9', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.58  thf('10', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf(t48_tex_2, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.58             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X27 : $i, X28 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.58          | (v3_tex_2 @ X27 @ X28)
% 0.20/0.58          | ~ (v2_tex_2 @ X27 @ X28)
% 0.20/0.58          | ~ (v1_tops_1 @ X27 @ X28)
% 0.20/0.58          | ~ (l1_pre_topc @ X28)
% 0.20/0.58          | ~ (v2_pre_topc @ X28)
% 0.20/0.58          | (v2_struct_0 @ X28))),
% 0.20/0.58      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v2_struct_0 @ X0)
% 0.20/0.58          | ~ (v2_pre_topc @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.58          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.58          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (((~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.20/0.58         | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.58         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58         | (v2_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.58  thf('14', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.58  thf(d2_tops_3, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.58             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X17 : $i, X18 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.58          | ((k2_pre_topc @ X18 @ X17) != (u1_struct_0 @ X18))
% 0.20/0.58          | (v1_tops_1 @ X17 @ X18)
% 0.20/0.58          | ~ (l1_pre_topc @ X18))),
% 0.20/0.58      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.58           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58           | (v1_tops_1 @ X0 @ sk_A)
% 0.20/0.58           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.58           | (v1_tops_1 @ X0 @ sk_A)
% 0.20/0.58           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_1))))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.20/0.58         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['14', '20'])).
% 0.20/0.58  thf('22', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf(d5_subset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X1 : $i, X2 : $i]:
% 0.20/0.58         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.58  thf(d6_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.58             ( v3_pre_topc @
% 0.20/0.58               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.20/0.58               A ) ) ) ) ))).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X11 : $i, X12 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.58          | ~ (v3_pre_topc @ 
% 0.20/0.58               (k7_subset_1 @ (u1_struct_0 @ X12) @ (k2_struct_0 @ X12) @ X11) @ 
% 0.20/0.58               X12)
% 0.20/0.58          | (v4_pre_topc @ X11 @ X12)
% 0.20/0.58          | ~ (l1_pre_topc @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (~ (v3_pre_topc @ 
% 0.20/0.58              (k7_subset_1 @ sk_B_1 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 0.20/0.58           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58           | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf(d3_struct_0, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (![X10 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (((((sk_B_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(dt_l1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      ((((sk_B_1) = (k2_struct_0 @ sk_A)))
% 0.20/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('demod', [status(thm)], ['30', '33'])).
% 0.20/0.58  thf('35', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.58          | ((k7_subset_1 @ X7 @ X6 @ X8) = (k4_xboole_0 @ X6 @ X8)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.58  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (~ (v3_pre_topc @ (k4_xboole_0 @ sk_B_1 @ X0) @ sk_A)
% 0.40/0.58           | (v4_pre_topc @ X0 @ sk_A)
% 0.40/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['27', '34', '37', '38', '39'])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (((~ (v3_pre_topc @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.40/0.58         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1))
% 0.40/0.58         | (v4_pre_topc @ sk_B_1 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['24', '40'])).
% 0.40/0.58  thf('42', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (((~ (v3_pre_topc @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.40/0.58         | (v4_pre_topc @ sk_B_1 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.58  thf('44', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.58  thf(dt_k3_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.40/0.58  thf(t17_tdlat_3, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ( v1_tdlat_3 @ A ) <=>
% 0.40/0.58         ( ![B:$i]:
% 0.40/0.58           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i]:
% 0.40/0.58         (~ (v1_tdlat_3 @ X21)
% 0.40/0.58          | (v3_pre_topc @ X22 @ X21)
% 0.40/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.58          | ~ (l1_pre_topc @ X21)
% 0.40/0.58          | ~ (v2_pre_topc @ X21))),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.40/0.58           | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58           | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58           | (v3_pre_topc @ X0 @ sk_A)
% 0.40/0.58           | ~ (v1_tdlat_3 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.58  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('52', plain, ((v1_tdlat_3 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.40/0.58           | (v3_pre_topc @ X0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (((v3_pre_topc @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ sk_A))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['46', '53'])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['43', '54'])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t52_pre_topc, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_pre_topc @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.40/0.58             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.40/0.58               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('57', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.40/0.58          | ~ (v4_pre_topc @ X14 @ X15)
% 0.40/0.58          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.40/0.58          | ~ (l1_pre_topc @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.40/0.58        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.40/0.58        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['55', '60'])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['21', '61'])).
% 0.40/0.58  thf('63', plain,
% 0.40/0.58      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('simplify', [status(thm)], ['62'])).
% 0.40/0.58  thf('64', plain,
% 0.40/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.40/0.58  thf('65', plain,
% 0.40/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.40/0.58  thf('66', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t43_tex_2, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.40/0.58         ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.40/0.58  thf('67', plain,
% 0.40/0.58      (![X23 : $i, X24 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.40/0.58          | (v2_tex_2 @ X23 @ X24)
% 0.40/0.58          | ~ (l1_pre_topc @ X24)
% 0.40/0.58          | ~ (v1_tdlat_3 @ X24)
% 0.40/0.58          | ~ (v2_pre_topc @ X24)
% 0.40/0.58          | (v2_struct_0 @ X24))),
% 0.40/0.58      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.40/0.58  thf('68', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (v1_tdlat_3 @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.40/0.58  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('70', plain, ((v1_tdlat_3 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('72', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.40/0.58  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('74', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.40/0.58      inference('clc', [status(thm)], ['72', '73'])).
% 0.40/0.58  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('77', plain,
% 0.40/0.58      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)],
% 0.40/0.58                ['13', '63', '64', '65', '74', '75', '76'])).
% 0.40/0.58  thf('78', plain,
% 0.40/0.58      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.40/0.58       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('split', [status(esa)], ['5'])).
% 0.40/0.58  thf('79', plain,
% 0.40/0.58      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('split', [status(esa)], ['5'])).
% 0.40/0.58  thf('80', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t47_tex_2, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.40/0.58             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.40/0.58  thf('81', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.40/0.58          | (v1_tops_1 @ X25 @ X26)
% 0.40/0.58          | ~ (v3_tex_2 @ X25 @ X26)
% 0.40/0.58          | ~ (v3_pre_topc @ X25 @ X26)
% 0.40/0.58          | ~ (l1_pre_topc @ X26)
% 0.40/0.58          | ~ (v2_pre_topc @ X26)
% 0.40/0.58          | (v2_struct_0 @ X26))),
% 0.40/0.58      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.40/0.58  thf('82', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.40/0.58        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.40/0.58        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['80', '81'])).
% 0.40/0.58  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('85', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('86', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i]:
% 0.40/0.58         (~ (v1_tdlat_3 @ X21)
% 0.40/0.58          | (v3_pre_topc @ X22 @ X21)
% 0.40/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.58          | ~ (l1_pre_topc @ X21)
% 0.40/0.58          | ~ (v2_pre_topc @ X21))),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.40/0.58  thf('87', plain,
% 0.40/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.40/0.58        | ~ (v1_tdlat_3 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['85', '86'])).
% 0.40/0.58  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('90', plain, ((v1_tdlat_3 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('91', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.40/0.58      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.40/0.58  thf('92', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.40/0.58        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['82', '83', '84', '91'])).
% 0.40/0.58  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('94', plain,
% 0.40/0.58      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('clc', [status(thm)], ['92', '93'])).
% 0.40/0.58  thf('95', plain,
% 0.40/0.58      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['79', '94'])).
% 0.40/0.58  thf('96', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('97', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.40/0.58          | ~ (v1_tops_1 @ X17 @ X18)
% 0.40/0.58          | ((k2_pre_topc @ X18 @ X17) = (u1_struct_0 @ X18))
% 0.40/0.58          | ~ (l1_pre_topc @ X18))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.40/0.58  thf('98', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.40/0.58        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.40/0.58  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('100', plain,
% 0.40/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.40/0.58        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['98', '99'])).
% 0.40/0.58  thf('101', plain,
% 0.40/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.40/0.58        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.40/0.58  thf('102', plain,
% 0.40/0.58      (![X10 : $i]:
% 0.40/0.58         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.58  thf('103', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('104', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup+', [status(thm)], ['102', '103'])).
% 0.40/0.58  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('106', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['104', '105'])).
% 0.40/0.58  thf('107', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.40/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.58  thf('108', plain,
% 0.40/0.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.40/0.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['106', '107'])).
% 0.40/0.58  thf('109', plain,
% 0.40/0.58      (![X10 : $i]:
% 0.40/0.58         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.58  thf('110', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.40/0.58          | ~ (v3_pre_topc @ 
% 0.40/0.58               (k7_subset_1 @ (u1_struct_0 @ X12) @ (k2_struct_0 @ X12) @ X11) @ 
% 0.40/0.58               X12)
% 0.40/0.58          | (v4_pre_topc @ X11 @ X12)
% 0.40/0.58          | ~ (l1_pre_topc @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.40/0.58  thf('111', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v3_pre_topc @ 
% 0.40/0.58             (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | (v4_pre_topc @ X1 @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['109', '110'])).
% 0.40/0.58  thf('112', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.58  thf('113', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | (v4_pre_topc @ X1 @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['111', '112'])).
% 0.40/0.58  thf('114', plain,
% 0.40/0.58      ((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.40/0.58        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['108', '113'])).
% 0.40/0.58  thf('115', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('118', plain,
% 0.40/0.58      ((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.40/0.58        | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.40/0.58  thf('119', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('120', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.58  thf('121', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['119', '120'])).
% 0.40/0.58  thf('122', plain,
% 0.40/0.58      (![X10 : $i]:
% 0.40/0.58         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.58  thf('123', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('124', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.40/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.58  thf('125', plain,
% 0.40/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.40/0.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['123', '124'])).
% 0.40/0.58  thf('126', plain,
% 0.40/0.58      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.40/0.58          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup+', [status(thm)], ['122', '125'])).
% 0.40/0.58  thf('127', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('128', plain,
% 0.40/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.40/0.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['126', '127'])).
% 0.40/0.58  thf('129', plain,
% 0.40/0.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.40/0.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['106', '107'])).
% 0.40/0.58  thf('130', plain,
% 0.40/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.40/0.58         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['128', '129'])).
% 0.40/0.58  thf('131', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['121', '130'])).
% 0.40/0.58  thf('132', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i]:
% 0.40/0.58         (~ (v1_tdlat_3 @ X21)
% 0.40/0.58          | (v3_pre_topc @ X22 @ X21)
% 0.40/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.58          | ~ (l1_pre_topc @ X21)
% 0.40/0.58          | ~ (v2_pre_topc @ X21))),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.40/0.58  thf('133', plain,
% 0.40/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.40/0.58        | ~ (v1_tdlat_3 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['131', '132'])).
% 0.40/0.58  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('136', plain, ((v1_tdlat_3 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('137', plain,
% 0.40/0.58      ((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.40/0.58      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 0.40/0.58  thf('138', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.40/0.58      inference('demod', [status(thm)], ['118', '137'])).
% 0.40/0.58  thf('139', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['101', '138'])).
% 0.40/0.58  thf('140', plain,
% 0.40/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A)) | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['100', '139'])).
% 0.40/0.58  thf('141', plain,
% 0.40/0.58      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['95', '140'])).
% 0.40/0.58  thf('142', plain,
% 0.40/0.58      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('143', plain,
% 0.40/0.58      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.40/0.58         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.40/0.58             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['141', '142'])).
% 0.40/0.58  thf(fc14_subset_1, axiom,
% 0.40/0.58    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.40/0.58  thf('144', plain, (![X9 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X9) @ X9)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.40/0.58  thf('145', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.58  thf('146', plain, (![X9 : $i]: ~ (v1_subset_1 @ X9 @ X9)),
% 0.40/0.58      inference('demod', [status(thm)], ['144', '145'])).
% 0.40/0.58  thf('147', plain,
% 0.40/0.58      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.40/0.58       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['143', '146'])).
% 0.40/0.58  thf('148', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['78', '147'])).
% 0.40/0.58  thf('149', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['77', '148'])).
% 0.40/0.58  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('151', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.40/0.58      inference('clc', [status(thm)], ['149', '150'])).
% 0.40/0.58  thf('152', plain, (($false) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['1', '151'])).
% 0.40/0.58  thf('153', plain,
% 0.40/0.58      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.40/0.58       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('154', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['78', '147', '153'])).
% 0.40/0.58  thf('155', plain, ($false),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['152', '154'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
