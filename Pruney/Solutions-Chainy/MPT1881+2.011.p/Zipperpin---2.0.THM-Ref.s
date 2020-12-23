%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTjOmb9LYg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:13 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  251 (1110 expanded)
%              Number of leaves         :   41 ( 330 expanded)
%              Depth                    :   22
%              Number of atoms          : 2028 (13427 expanded)
%              Number of equality atoms :   83 ( 275 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(rc4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_tops_1 @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X21: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_tdlat_3 @ X27 )
      | ( v3_pre_topc @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('41',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['6','55'])).

thf('57',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_tops_1 @ X31 @ X32 )
      | ~ ( v3_tex_2 @ X31 @ X32 )
      | ~ ( v3_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_tdlat_3 @ X27 )
      | ( v3_pre_topc @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('66',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v3_pre_topc @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('82',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('83',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','73'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_tops_1 @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ! [X0: $i] :
        ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('105',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
        = ( sk_B @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','110'])).

thf('112',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( sk_B @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( sk_B @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['80','114'])).

thf('116',plain,
    ( ( sk_B_2
      = ( sk_B @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['56','115'])).

thf('117',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( sk_B @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('119',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( ( v1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( sk_B @ sk_A ) )
   <= ( ( v3_tex_2 @ sk_B_2 @ sk_A )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['117','122'])).

thf('124',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( ( v3_tex_2 @ sk_B_2 @ sk_A )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['116','123'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('125',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('126',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('127',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ X12 @ X12 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('130',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('131',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26 = X25 )
      | ( v1_subset_1 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('132',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('134',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

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

thf('136',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v3_tex_2 @ X33 @ X34 )
      | ~ ( v2_tex_2 @ X33 @ X34 )
      | ~ ( v1_tops_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
      | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('140',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('141',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_pre_topc @ X24 @ X23 )
       != ( u1_struct_0 @ X24 ) )
      | ( v1_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
       != sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','145'])).

thf('147',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('148',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('149',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k7_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k7_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ! [X21: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('155',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('156',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('157',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('161',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_tops_1 @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_tops_1 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('165',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = sk_B_2 )
        | ~ ( v1_tops_1 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( ( ~ ( v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','165'])).

thf('167',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
      = sk_B_2 )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('171',plain,
    ( ( ( sk_B_2
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( sk_B_2
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('176',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('177',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_tdlat_3 @ X27 )
      | ( v3_pre_topc @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('178',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( v3_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['178','179','180','181'])).

thf('183',plain,
    ( ! [X0: $i] :
        ( v3_pre_topc @ ( k4_xboole_0 @ sk_B_2 @ X0 ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','182'])).

thf('184',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','173','174','183'])).

thf('185',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','184'])).

thf('186',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('187',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','187'])).

thf('189',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('191',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('192',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('193',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_tdlat_3 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( v3_tex_2 @ sk_B_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','189','190','191','200','201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('207',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','128','129','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTjOmb9LYg
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:18:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 381 iterations in 0.224s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.48/0.68  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.48/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.48/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.48/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.48/0.68  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.48/0.68  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.48/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.48/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.48/0.68  thf(t49_tex_2, conjecture,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.48/0.68         ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v3_tex_2 @ B @ A ) <=>
% 0.48/0.68             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i]:
% 0.48/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.68            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68          ( ![B:$i]:
% 0.48/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68              ( ( v3_tex_2 @ B @ A ) <=>
% 0.48/0.68                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.48/0.68        | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.48/0.68       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t52_pre_topc, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.48/0.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.48/0.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.68          | ~ (v4_pre_topc @ X17 @ X18)
% 0.48/0.68          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.48/0.68          | ~ (l1_pre_topc @ X18))),
% 0.48/0.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.48/0.68        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.68  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.48/0.68        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.48/0.68  thf(rc4_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ?[B:$i]:
% 0.48/0.68         ( ( v1_tops_1 @ B @ A ) & 
% 0.48/0.68           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      (![X21 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (sk_B @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.48/0.68          | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf(d2_tops_3, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v1_tops_1 @ B @ A ) <=>
% 0.48/0.68             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X23 : $i, X24 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.48/0.68          | ~ (v1_tops_1 @ X23 @ X24)
% 0.48/0.68          | ((k2_pre_topc @ X24 @ X23) = (u1_struct_0 @ X24))
% 0.48/0.68          | ~ (l1_pre_topc @ X24))),
% 0.48/0.68      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (u1_struct_0 @ X0))
% 0.48/0.68          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (u1_struct_0 @ X0))
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X21 : $i]: ((v1_tops_1 @ (sk_B @ X21) @ X21) | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('clc', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (![X21 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (sk_B @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.48/0.68          | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf(d3_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v1_tops_1 @ B @ A ) <=>
% 0.48/0.68             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.48/0.68  thf('14', plain,
% 0.48/0.68      (![X19 : $i, X20 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.48/0.68          | ~ (v1_tops_1 @ X19 @ X20)
% 0.48/0.68          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.48/0.68          | ~ (l1_pre_topc @ X20))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0))
% 0.48/0.68          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0))
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['15'])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X21 : $i]: ((v1_tops_1 @ (sk_B @ X21) @ X21) | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0)))),
% 0.48/0.68      inference('clc', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['12', '18'])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['19'])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.68      inference('sup+', [status(thm)], ['20', '21'])).
% 0.48/0.68  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('24', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['19'])).
% 0.48/0.68  thf(t36_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.48/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.48/0.68  thf(d1_zfmisc_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.48/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.68         (~ (r1_tarski @ X2 @ X3)
% 0.48/0.68          | (r2_hidden @ X2 @ X4)
% 0.48/0.68          | ((X4) != (k1_zfmisc_1 @ X3)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      (![X2 : $i, X3 : $i]:
% 0.48/0.68         ((r2_hidden @ X2 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X2 @ X3))),
% 0.48/0.68      inference('simplify', [status(thm)], ['27'])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['26', '28'])).
% 0.48/0.68  thf(t1_subset, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.48/0.68      inference('cnf', [status(esa)], [t1_subset])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.68  thf(t17_tdlat_3, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ( v1_tdlat_3 @ A ) <=>
% 0.48/0.68         ( ![B:$i]:
% 0.48/0.68           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X27 : $i, X28 : $i]:
% 0.48/0.68         (~ (v1_tdlat_3 @ X27)
% 0.48/0.68          | (v3_pre_topc @ X28 @ X27)
% 0.48/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.48/0.68          | ~ (l1_pre_topc @ X27)
% 0.48/0.68          | ~ (v2_pre_topc @ X27))),
% 0.48/0.68      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.48/0.68          | ~ (v1_tdlat_3 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v2_pre_topc @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['25', '33'])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['19'])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['19'])).
% 0.48/0.68  thf(d6_pre_topc, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v4_pre_topc @ B @ A ) <=>
% 0.48/0.68             ( v3_pre_topc @
% 0.48/0.68               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.48/0.68               A ) ) ) ) ))).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.48/0.68          | ~ (v3_pre_topc @ 
% 0.48/0.68               (k7_subset_1 @ (u1_struct_0 @ X16) @ (k2_struct_0 @ X16) @ X15) @ 
% 0.48/0.68               X16)
% 0.48/0.68          | (v4_pre_topc @ X15 @ X16)
% 0.48/0.68          | ~ (l1_pre_topc @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v3_pre_topc @ 
% 0.48/0.68             (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v4_pre_topc @ X1 @ X0)
% 0.48/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.68  thf(dt_k2_subset_1, axiom,
% 0.48/0.68    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.48/0.68  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.68  thf('41', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.48/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.68  thf('42', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.48/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.48/0.68  thf(redefinition_k7_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.48/0.68  thf('43', plain,
% 0.48/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.48/0.68          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.48/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v4_pre_topc @ X1 @ X0)
% 0.48/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.48/0.68      inference('demod', [status(thm)], ['39', '44'])).
% 0.48/0.68  thf('46', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.68          | (v4_pre_topc @ X1 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['45'])).
% 0.48/0.68  thf('47', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v4_pre_topc @ X1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['36', '46'])).
% 0.48/0.68  thf('48', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((v4_pre_topc @ X1 @ X0)
% 0.48/0.68          | ~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['47'])).
% 0.48/0.68  thf('49', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.68          | ~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v4_pre_topc @ X1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['35', '48'])).
% 0.48/0.68  thf('50', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((v4_pre_topc @ X1 @ X0)
% 0.48/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.48/0.68          | ~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['49'])).
% 0.48/0.68  thf('51', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ~ (v1_tdlat_3 @ sk_A)
% 0.48/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68        | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['24', '50'])).
% 0.48/0.68  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('53', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('55', plain, ((v4_pre_topc @ sk_B_2 @ sk_A)),
% 0.48/0.68      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.48/0.68  thf('56', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.48/0.68      inference('demod', [status(thm)], ['6', '55'])).
% 0.48/0.68  thf('57', plain,
% 0.48/0.68      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.48/0.68        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('58', plain,
% 0.48/0.68      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['57'])).
% 0.48/0.68  thf('59', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t47_tex_2, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.48/0.68             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.48/0.68  thf('60', plain,
% 0.48/0.68      (![X31 : $i, X32 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.48/0.68          | (v1_tops_1 @ X31 @ X32)
% 0.48/0.68          | ~ (v3_tex_2 @ X31 @ X32)
% 0.48/0.68          | ~ (v3_pre_topc @ X31 @ X32)
% 0.48/0.68          | ~ (l1_pre_topc @ X32)
% 0.48/0.68          | ~ (v2_pre_topc @ X32)
% 0.48/0.68          | (v2_struct_0 @ X32))),
% 0.48/0.68      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.48/0.68  thf('61', plain,
% 0.48/0.68      (((v2_struct_0 @ sk_A)
% 0.48/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.48/0.68        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.68        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.48/0.68  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('64', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('65', plain,
% 0.48/0.68      (![X27 : $i, X28 : $i]:
% 0.48/0.68         (~ (v1_tdlat_3 @ X27)
% 0.48/0.68          | (v3_pre_topc @ X28 @ X27)
% 0.48/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.48/0.68          | ~ (l1_pre_topc @ X27)
% 0.48/0.68          | ~ (v2_pre_topc @ X27))),
% 0.48/0.68      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.48/0.68  thf('66', plain,
% 0.48/0.68      ((~ (v2_pre_topc @ sk_A)
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.48/0.68        | ~ (v1_tdlat_3 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['64', '65'])).
% 0.48/0.68  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('69', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('70', plain, ((v3_pre_topc @ sk_B_2 @ sk_A)),
% 0.48/0.68      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.48/0.68  thf('71', plain,
% 0.48/0.68      (((v2_struct_0 @ sk_A)
% 0.48/0.68        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.68        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['61', '62', '63', '70'])).
% 0.48/0.68  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('73', plain,
% 0.48/0.68      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('clc', [status(thm)], ['71', '72'])).
% 0.48/0.68  thf('74', plain,
% 0.48/0.68      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['58', '73'])).
% 0.48/0.68  thf('75', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('76', plain,
% 0.48/0.68      (![X19 : $i, X20 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.48/0.68          | ~ (v1_tops_1 @ X19 @ X20)
% 0.48/0.68          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.48/0.68          | ~ (l1_pre_topc @ X20))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.48/0.68  thf('77', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A))
% 0.48/0.68        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['75', '76'])).
% 0.48/0.68  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('79', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A))
% 0.48/0.68        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['77', '78'])).
% 0.48/0.68  thf('80', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['74', '79'])).
% 0.48/0.68  thf('81', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('clc', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('82', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['74', '79'])).
% 0.48/0.68  thf('83', plain,
% 0.48/0.68      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['58', '73'])).
% 0.48/0.68  thf('84', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('85', plain,
% 0.48/0.68      (![X23 : $i, X24 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.48/0.68          | ~ (v1_tops_1 @ X23 @ X24)
% 0.48/0.68          | ((k2_pre_topc @ X24 @ X23) = (u1_struct_0 @ X24))
% 0.48/0.68          | ~ (l1_pre_topc @ X24))),
% 0.48/0.68      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.48/0.68  thf('86', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.48/0.68        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['84', '85'])).
% 0.48/0.68  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('88', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.48/0.68        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['86', '87'])).
% 0.48/0.68  thf('89', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['83', '88'])).
% 0.48/0.68  thf('90', plain,
% 0.48/0.68      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['82', '89'])).
% 0.48/0.68  thf('91', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.48/0.68          | ~ (v1_tdlat_3 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf('92', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          ((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 0.48/0.68           | ~ (v1_tdlat_3 @ sk_A)
% 0.48/0.68           | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68           | ~ (v2_pre_topc @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['90', '91'])).
% 0.48/0.68  thf('93', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('96', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.48/0.68  thf('97', plain,
% 0.48/0.68      (![X21 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (sk_B @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.48/0.68          | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf('98', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.68          | (v4_pre_topc @ X1 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['45'])).
% 0.48/0.68  thf('99', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v3_pre_topc @ 
% 0.48/0.68               (k4_xboole_0 @ (k2_struct_0 @ X0) @ (sk_B @ X0)) @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | (v4_pre_topc @ (sk_B @ X0) @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['97', '98'])).
% 0.48/0.68  thf('100', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.48/0.68          | ~ (v3_pre_topc @ 
% 0.48/0.68               (k4_xboole_0 @ (k2_struct_0 @ X0) @ (sk_B @ X0)) @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['99'])).
% 0.48/0.68  thf('101', plain,
% 0.48/0.68      (((~ (l1_pre_topc @ sk_A) | (v4_pre_topc @ (sk_B @ sk_A) @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['96', '100'])).
% 0.48/0.68  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('103', plain,
% 0.48/0.68      (((v4_pre_topc @ (sk_B @ sk_A) @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['101', '102'])).
% 0.48/0.68  thf('104', plain,
% 0.48/0.68      (![X21 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (sk_B @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.48/0.68          | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf('105', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.68          | ~ (v4_pre_topc @ X17 @ X18)
% 0.48/0.68          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.48/0.68          | ~ (l1_pre_topc @ X18))),
% 0.48/0.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.48/0.68  thf('106', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (sk_B @ X0))
% 0.48/0.68          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['104', '105'])).
% 0.48/0.68  thf('107', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (sk_B @ X0))
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['106'])).
% 0.48/0.68  thf('108', plain,
% 0.48/0.68      (((~ (l1_pre_topc @ sk_A)
% 0.48/0.68         | ((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A))))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['103', '107'])).
% 0.48/0.68  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('110', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['108', '109'])).
% 0.48/0.68  thf('111', plain,
% 0.48/0.68      (((((u1_struct_0 @ sk_A) = (sk_B @ sk_A)) | ~ (l1_pre_topc @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['81', '110'])).
% 0.48/0.68  thf('112', plain,
% 0.48/0.68      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['82', '89'])).
% 0.48/0.68  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('114', plain,
% 0.48/0.68      ((((k2_struct_0 @ sk_A) = (sk_B @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.48/0.68  thf('115', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['80', '114'])).
% 0.48/0.68  thf('116', plain,
% 0.48/0.68      ((((sk_B_2) = (sk_B @ sk_A))) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['56', '115'])).
% 0.48/0.68  thf('117', plain,
% 0.48/0.68      ((((k2_struct_0 @ sk_A) = (sk_B @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.48/0.68  thf('118', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['19'])).
% 0.48/0.68  thf('119', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('120', plain,
% 0.48/0.68      ((((v1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A)))
% 0.48/0.68         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['118', '119'])).
% 0.48/0.68  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('122', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A)))
% 0.48/0.68         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['120', '121'])).
% 0.48/0.68  thf('123', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ (sk_B @ sk_A)))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)) & 
% 0.48/0.68             ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['117', '122'])).
% 0.48/0.68  thf('124', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ sk_B_2))
% 0.48/0.68         <= (((v3_tex_2 @ sk_B_2 @ sk_A)) & 
% 0.48/0.68             ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['116', '123'])).
% 0.48/0.68  thf(fc14_subset_1, axiom,
% 0.48/0.68    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.48/0.68  thf('125', plain, (![X12 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X12) @ X12)),
% 0.48/0.68      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.48/0.68  thf('126', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.48/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.68  thf('127', plain, (![X12 : $i]: ~ (v1_subset_1 @ X12 @ X12)),
% 0.48/0.68      inference('demod', [status(thm)], ['125', '126'])).
% 0.48/0.68  thf('128', plain,
% 0.48/0.68      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.48/0.68       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['124', '127'])).
% 0.48/0.68  thf('129', plain,
% 0.48/0.68      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.48/0.68       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['57'])).
% 0.48/0.68  thf('130', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(d7_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.48/0.68  thf('131', plain,
% 0.48/0.68      (![X25 : $i, X26 : $i]:
% 0.48/0.68         (((X26) = (X25))
% 0.48/0.68          | (v1_subset_1 @ X26 @ X25)
% 0.48/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.48/0.68  thf('132', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.48/0.68        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['130', '131'])).
% 0.48/0.68  thf('133', plain,
% 0.48/0.68      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('split', [status(esa)], ['57'])).
% 0.48/0.68  thf('134', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('135', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.48/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.48/0.68  thf(t48_tex_2, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.48/0.68             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.48/0.68  thf('136', plain,
% 0.48/0.68      (![X33 : $i, X34 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.48/0.68          | (v3_tex_2 @ X33 @ X34)
% 0.48/0.68          | ~ (v2_tex_2 @ X33 @ X34)
% 0.48/0.68          | ~ (v1_tops_1 @ X33 @ X34)
% 0.48/0.68          | ~ (l1_pre_topc @ X34)
% 0.48/0.68          | ~ (v2_pre_topc @ X34)
% 0.48/0.68          | (v2_struct_0 @ X34))),
% 0.48/0.68      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.48/0.68  thf('137', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((v2_struct_0 @ X0)
% 0.48/0.68          | ~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.68          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.68          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['135', '136'])).
% 0.48/0.68  thf('138', plain,
% 0.48/0.68      (((~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 0.48/0.68         | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.48/0.68         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.48/0.68         | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68         | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68         | (v2_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['134', '137'])).
% 0.48/0.68  thf('139', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.48/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.48/0.68  thf('140', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('141', plain,
% 0.48/0.68      (![X23 : $i, X24 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.48/0.68          | ((k2_pre_topc @ X24 @ X23) != (u1_struct_0 @ X24))
% 0.48/0.68          | (v1_tops_1 @ X23 @ X24)
% 0.48/0.68          | ~ (l1_pre_topc @ X24))),
% 0.48/0.68      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.48/0.68  thf('142', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.68           | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68           | (v1_tops_1 @ X0 @ sk_A)
% 0.48/0.68           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['140', '141'])).
% 0.48/0.68  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('144', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('145', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.68           | (v1_tops_1 @ X0 @ sk_A)
% 0.48/0.68           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_2))))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.48/0.68  thf('146', plain,
% 0.48/0.68      (((((k2_pre_topc @ sk_A @ sk_B_2) != (sk_B_2))
% 0.48/0.68         | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['139', '145'])).
% 0.48/0.68  thf('147', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.48/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.48/0.68  thf('148', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('149', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.48/0.68          | ~ (v3_pre_topc @ 
% 0.48/0.68               (k7_subset_1 @ (u1_struct_0 @ X16) @ (k2_struct_0 @ X16) @ X15) @ 
% 0.48/0.68               X16)
% 0.48/0.68          | (v4_pre_topc @ X15 @ X16)
% 0.48/0.68          | ~ (l1_pre_topc @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.48/0.68  thf('150', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (v3_pre_topc @ 
% 0.48/0.68              (k7_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 0.48/0.68           | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68           | (v4_pre_topc @ X0 @ sk_A)
% 0.48/0.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['148', '149'])).
% 0.48/0.68  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('152', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('153', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (v3_pre_topc @ 
% 0.48/0.68              (k7_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 0.48/0.68           | (v4_pre_topc @ X0 @ sk_A)
% 0.48/0.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.48/0.68  thf('154', plain,
% 0.48/0.68      (![X21 : $i]: ((v1_tops_1 @ (sk_B @ X21) @ X21) | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf('155', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('156', plain,
% 0.48/0.68      (![X21 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (sk_B @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.48/0.68          | ~ (l1_pre_topc @ X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.48/0.68  thf('157', plain,
% 0.48/0.68      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.68         | ~ (l1_pre_topc @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['155', '156'])).
% 0.48/0.68  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('159', plain,
% 0.48/0.68      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_2)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['157', '158'])).
% 0.48/0.68  thf('160', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('161', plain,
% 0.48/0.68      (![X23 : $i, X24 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.48/0.68          | ~ (v1_tops_1 @ X23 @ X24)
% 0.48/0.68          | ((k2_pre_topc @ X24 @ X23) = (u1_struct_0 @ X24))
% 0.48/0.68          | ~ (l1_pre_topc @ X24))),
% 0.48/0.68      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.48/0.68  thf('162', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.68           | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68           | ((k2_pre_topc @ sk_A @ X0) = (u1_struct_0 @ sk_A))
% 0.48/0.68           | ~ (v1_tops_1 @ X0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['160', '161'])).
% 0.48/0.68  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('164', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('165', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.68           | ((k2_pre_topc @ sk_A @ X0) = (sk_B_2))
% 0.48/0.68           | ~ (v1_tops_1 @ X0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.48/0.68  thf('166', plain,
% 0.48/0.68      (((~ (v1_tops_1 @ (sk_B @ sk_A) @ sk_A)
% 0.48/0.68         | ((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (sk_B_2))))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['159', '165'])).
% 0.48/0.68  thf('167', plain,
% 0.48/0.68      (((~ (l1_pre_topc @ sk_A)
% 0.48/0.68         | ((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (sk_B_2))))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['154', '166'])).
% 0.48/0.68  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('169', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (sk_B_2)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['167', '168'])).
% 0.48/0.68  thf('170', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0)))),
% 0.48/0.68      inference('clc', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf('171', plain,
% 0.48/0.68      (((((sk_B_2) = (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['169', '170'])).
% 0.48/0.68  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('173', plain,
% 0.48/0.68      ((((sk_B_2) = (k2_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['171', '172'])).
% 0.48/0.68  thf('174', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.48/0.68  thf('175', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.68  thf('176', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('177', plain,
% 0.48/0.68      (![X27 : $i, X28 : $i]:
% 0.48/0.68         (~ (v1_tdlat_3 @ X27)
% 0.48/0.68          | (v3_pre_topc @ X28 @ X27)
% 0.48/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.48/0.68          | ~ (l1_pre_topc @ X27)
% 0.48/0.68          | ~ (v2_pre_topc @ X27))),
% 0.48/0.68      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.48/0.68  thf('178', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.68           | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68           | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68           | (v3_pre_topc @ X0 @ sk_A)
% 0.48/0.68           | ~ (v1_tdlat_3 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['176', '177'])).
% 0.48/0.68  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('181', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('182', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.68           | (v3_pre_topc @ X0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['178', '179', '180', '181'])).
% 0.48/0.68  thf('183', plain,
% 0.48/0.68      ((![X0 : $i]: (v3_pre_topc @ (k4_xboole_0 @ sk_B_2 @ X0) @ sk_A))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['175', '182'])).
% 0.48/0.68  thf('184', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          ((v4_pre_topc @ X0 @ sk_A)
% 0.48/0.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['153', '173', '174', '183'])).
% 0.48/0.68  thf('185', plain,
% 0.48/0.68      (((v4_pre_topc @ sk_B_2 @ sk_A))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['147', '184'])).
% 0.48/0.68  thf('186', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.48/0.68        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.48/0.68  thf('187', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['185', '186'])).
% 0.48/0.68  thf('188', plain,
% 0.48/0.68      (((((sk_B_2) != (sk_B_2)) | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['146', '187'])).
% 0.48/0.68  thf('189', plain,
% 0.48/0.68      (((v1_tops_1 @ sk_B_2 @ sk_A))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['188'])).
% 0.48/0.68  thf('190', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('191', plain,
% 0.48/0.68      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.68  thf('192', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t43_tex_2, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.48/0.68         ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.48/0.68  thf('193', plain,
% 0.48/0.68      (![X29 : $i, X30 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.48/0.68          | (v2_tex_2 @ X29 @ X30)
% 0.48/0.68          | ~ (l1_pre_topc @ X30)
% 0.48/0.68          | ~ (v1_tdlat_3 @ X30)
% 0.48/0.68          | ~ (v2_pre_topc @ X30)
% 0.48/0.68          | (v2_struct_0 @ X30))),
% 0.48/0.68      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.48/0.68  thf('194', plain,
% 0.48/0.68      (((v2_struct_0 @ sk_A)
% 0.48/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68        | ~ (v1_tdlat_3 @ sk_A)
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['192', '193'])).
% 0.48/0.68  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('196', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('198', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 0.48/0.68  thf('199', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('200', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.48/0.68      inference('clc', [status(thm)], ['198', '199'])).
% 0.48/0.68  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('202', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('203', plain,
% 0.48/0.68      ((((v3_tex_2 @ sk_B_2 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)],
% 0.48/0.68                ['138', '189', '190', '191', '200', '201', '202'])).
% 0.48/0.68  thf('204', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('205', plain,
% 0.48/0.68      (((v3_tex_2 @ sk_B_2 @ sk_A))
% 0.48/0.68         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('clc', [status(thm)], ['203', '204'])).
% 0.48/0.68  thf('206', plain,
% 0.48/0.68      ((~ (v3_tex_2 @ sk_B_2 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('207', plain,
% 0.48/0.68      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.48/0.68       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['205', '206'])).
% 0.48/0.68  thf('208', plain, ($false),
% 0.48/0.68      inference('sat_resolution*', [status(thm)], ['1', '128', '129', '207'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
