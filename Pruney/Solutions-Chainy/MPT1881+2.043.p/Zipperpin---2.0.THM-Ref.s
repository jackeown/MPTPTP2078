%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5OEsBuLvw

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 318 expanded)
%              Number of leaves         :   26 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          :  997 (3680 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X6 ) @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

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

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( v1_subset_1 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('16',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_tex_2 @ X9 @ X10 )
      | ~ ( v2_tex_2 @ X11 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( X9 = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( sk_B @ X0 )
        = X1 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ( ( sk_B @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,
    ( ( ~ ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 )
      | ~ ( v3_tex_2 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ( ( sk_B @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('31',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ~ ( v3_tex_2 @ ( sk_B @ sk_A ) @ sk_A )
      | ( ( sk_B @ sk_A )
        = sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','35','36','45','46','47'])).

thf('49',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('50',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('54',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_tex_2 @ X9 @ X10 )
      | ~ ( v2_tex_2 @ X11 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( X9 = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( sk_B_1 = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['72','74'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('76',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('78',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ X2 @ X2 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['49','79'])).

thf('81',plain,
    ( ~ ( v3_tex_2 @ ( sk_B @ sk_A ) @ sk_A )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['48','80'])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('90',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['73'])).

thf('96',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['73'])).

thf('97',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','79','96'])).

thf('98',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('99',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['94','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5OEsBuLvw
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 195 iterations in 0.080s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(t49_tex_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.22/0.54         ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.54            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54              ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.22/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(rc4_tops_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ?[B:$i]:
% 0.22/0.54         ( ( v1_tops_1 @ B @ A ) & 
% 0.22/0.54           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X6 : $i]: ((v1_tops_1 @ (sk_B @ X6) @ X6) | ~ (l1_pre_topc @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X6 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.54          | ~ (l1_pre_topc @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.22/0.54  thf(t43_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.22/0.54         ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.54          | (v2_tex_2 @ X14 @ X15)
% 0.22/0.54          | ~ (l1_pre_topc @ X15)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X15)
% 0.22/0.54          | ~ (v2_pre_topc @ X15)
% 0.22/0.54          | (v2_struct_0 @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_tex_2 @ (sk_B @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X6 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.54          | ~ (l1_pre_topc @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.22/0.54  thf(t48_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.22/0.54             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | (v3_tex_2 @ X16 @ X17)
% 0.22/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.22/0.54          | ~ (v1_tops_1 @ X16 @ X17)
% 0.22/0.54          | ~ (l1_pre_topc @ X17)
% 0.22/0.54          | ~ (v2_pre_topc @ X17)
% 0.22/0.54          | (v2_struct_0 @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '9'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d7_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X7 : $i, X8 : $i]:
% 0.22/0.54         (((X8) = (X7))
% 0.22/0.54          | (v1_subset_1 @ X8 @ X7)
% 0.22/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '18'])).
% 0.22/0.54  thf(dt_k2_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.54  thf('21', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('22', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X6 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.54          | ~ (l1_pre_topc @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.22/0.54  thf(d7_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.54               ( ![C:$i]:
% 0.22/0.54                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.54                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.54          | ~ (v3_tex_2 @ X9 @ X10)
% 0.22/0.54          | ~ (v2_tex_2 @ X11 @ X10)
% 0.22/0.54          | ~ (r1_tarski @ X9 @ X11)
% 0.22/0.54          | ((X9) = (X11))
% 0.22/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.54          | ~ (l1_pre_topc @ X10))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | ((sk_B @ X0) = (X1))
% 0.22/0.54          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.22/0.54          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.54          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.54          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.22/0.54          | ((sk_B @ X0) = (X1))
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (((~ (r1_tarski @ (sk_B @ sk_A) @ sk_B_1)
% 0.22/0.54         | ~ (v3_tex_2 @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.54         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.22/0.54         | ((sk_B @ sk_A) = (u1_struct_0 @ sk_A))
% 0.22/0.54         | ~ (l1_pre_topc @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['19', '27'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '18'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X6 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.54          | ~ (l1_pre_topc @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))
% 0.22/0.54         | ~ (l1_pre_topc @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_1)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_1))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '18'])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.54          | (v2_tex_2 @ X14 @ X15)
% 0.22/0.54          | ~ (l1_pre_topc @ X15)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X15)
% 0.22/0.54          | ~ (v2_pre_topc @ X15)
% 0.22/0.54          | (v2_struct_0 @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.54  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('41', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('43', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.22/0.54  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('45', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '18'])).
% 0.22/0.54  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (((~ (v3_tex_2 @ (sk_B @ sk_A) @ sk_A) | ((sk_B @ sk_A) = (sk_B_1))))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['28', '35', '36', '45', '46', '47'])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.22/0.54       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('split', [status(esa)], ['17'])).
% 0.22/0.54  thf('50', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.54          | (v2_tex_2 @ X14 @ X15)
% 0.22/0.54          | ~ (l1_pre_topc @ X15)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X15)
% 0.22/0.54          | ~ (v2_pre_topc @ X15)
% 0.22/0.54          | (v2_struct_0 @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.54  thf('53', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['17'])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.54          | ~ (v3_tex_2 @ X9 @ X10)
% 0.22/0.54          | ~ (v2_tex_2 @ X11 @ X10)
% 0.22/0.54          | ~ (r1_tarski @ X9 @ X11)
% 0.22/0.54          | ((X9) = (X11))
% 0.22/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.54          | ~ (l1_pre_topc @ X10))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((sk_B_1) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.54  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((sk_B_1) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54           | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.22/0.54           | ((sk_B_1) = (X0))
% 0.22/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['54', '59'])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.54         | ~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.54         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['53', '60'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('64', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.54         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['61', '64'])).
% 0.22/0.54  thf('66', plain,
% 0.22/0.54      (((~ (l1_pre_topc @ sk_A)
% 0.22/0.54         | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54         | (v2_struct_0 @ sk_A)
% 0.22/0.54         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['52', '65'])).
% 0.22/0.54  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('68', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.22/0.54  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('72', plain,
% 0.22/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['70', '71'])).
% 0.22/0.54  thf('73', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('74', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['73'])).
% 0.22/0.54  thf('75', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.22/0.54             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['72', '74'])).
% 0.22/0.54  thf(fc14_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.22/0.54  thf('76', plain, (![X2 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X2) @ X2)),
% 0.22/0.54      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.22/0.54  thf('77', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('78', plain, (![X2 : $i]: ~ (v1_subset_1 @ X2 @ X2)),
% 0.22/0.54      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.54  thf('79', plain,
% 0.22/0.54      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.22/0.54       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['75', '78'])).
% 0.22/0.54  thf('80', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['49', '79'])).
% 0.22/0.54  thf('81', plain,
% 0.22/0.54      ((~ (v3_tex_2 @ (sk_B @ sk_A) @ sk_A) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['48', '80'])).
% 0.22/0.54  thf('82', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.54        | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '81'])).
% 0.22/0.54  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('85', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('86', plain, (((v2_struct_0 @ sk_A) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.22/0.54  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('88', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.22/0.54      inference('clc', [status(thm)], ['86', '87'])).
% 0.22/0.54  thf('89', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.54  thf('90', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v1_tdlat_3 @ sk_A))),
% 0.22/0.54      inference('sup+', [status(thm)], ['88', '89'])).
% 0.22/0.54  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('93', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('94', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.22/0.54  thf('95', plain,
% 0.22/0.54      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['73'])).
% 0.22/0.54  thf('96', plain,
% 0.22/0.54      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.22/0.54       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['73'])).
% 0.22/0.54  thf('97', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['49', '79', '96'])).
% 0.22/0.54  thf('98', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['95', '97'])).
% 0.22/0.54  thf('99', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('clc', [status(thm)], ['94', '98'])).
% 0.22/0.54  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
