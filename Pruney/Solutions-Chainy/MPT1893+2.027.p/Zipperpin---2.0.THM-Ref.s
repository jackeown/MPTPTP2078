%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OGZISWkl9f

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 (1020 expanded)
%              Number of leaves         :   27 ( 293 expanded)
%              Depth                    :   19
%              Number of atoms          :  900 (16085 expanded)
%              Number of equality atoms :   26 ( 153 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_tdlat_3 @ X9 )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('5',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_tops_1 @ X13 @ X14 )
      | ~ ( v3_tex_2 @ X13 @ X14 )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v1_tops_1 @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v4_pre_topc @ X0 @ X1 )
      | ( ( k2_pre_topc @ X1 @ X0 )
        = X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v1_tdlat_3 @ X12 )
      | ( X11
       != ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v1_tdlat_3 @ X12 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X12 ) @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_tex_2 @ X4 @ X5 )
      | ( v2_tex_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ( v1_tdlat_3 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39','45','46'])).

thf('48',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('52',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('53',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_tdlat_3 @ X7 )
      | ~ ( v3_pre_topc @ X8 @ X7 )
      | ( v4_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('59',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('66',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v1_tdlat_3 @ X12 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X12 ) @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('69',plain,
    ( ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('71',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('72',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ( v1_tdlat_3 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( v1_tdlat_3 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_tex_2 @ X15 @ X16 )
      | ~ ( v1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v1_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_tex_2])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['78','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('93',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['50','93'])).

thf('95',plain,
    ( ( ( v1_tdlat_3 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['47','94'])).

thf('96',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('97',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('99',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OGZISWkl9f
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 110 iterations in 0.054s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.51  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(t61_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.51                ( v3_tex_2 @ B @ A ) & 
% 0.21/0.51                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.51                   ( v3_tex_2 @ B @ A ) & 
% 0.21/0.51                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['1'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t24_tdlat_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.51         ( ![B:$i]:
% 0.21/0.51           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (v3_tdlat_3 @ X9)
% 0.21/0.51          | ~ (v4_pre_topc @ X10 @ X9)
% 0.21/0.51          | (v3_pre_topc @ X10 @ X9)
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.51          | ~ (l1_pre_topc @ X9)
% 0.21/0.51          | ~ (v2_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.51        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t47_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.21/0.51             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | (v1_tops_1 @ X13 @ X14)
% 0.21/0.51          | ~ (v3_tex_2 @ X13 @ X14)
% 0.21/0.51          | ~ (v3_pre_topc @ X13 @ X14)
% 0.21/0.51          | ~ (l1_pre_topc @ X14)
% 0.21/0.51          | ~ (v2_pre_topc @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.51        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.21/0.51        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.51        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.21/0.51  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_tops_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.51             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.21/0.51          | ~ (v1_tops_1 @ X2 @ X3)
% 0.21/0.51          | ((k2_pre_topc @ X3 @ X2) = (u1_struct_0 @ X3))
% 0.21/0.51          | ~ (l1_pre_topc @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['1'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t52_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.51             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.51               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.51          | ~ (v4_pre_topc @ X0 @ X1)
% 0.21/0.51          | ((k2_pre_topc @ X1 @ X0) = (X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.21/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.21/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.21/0.51         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '33'])).
% 0.21/0.51  thf(t27_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.21/0.51             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.51          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.51          | (v1_tdlat_3 @ X12)
% 0.21/0.51          | ((X11) != (u1_struct_0 @ X12))
% 0.21/0.51          | ~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t27_tex_2])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X12 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X12)
% 0.21/0.51          | ~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v1_tdlat_3 @ X12)
% 0.21/0.51          | ~ (v2_tex_2 @ (u1_struct_0 @ X12) @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.51         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.51         | (v1_tdlat_3 @ sk_A)
% 0.21/0.51         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '33'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '33'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d7_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.51             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.51               ( ![C:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.51          | ~ (v3_tex_2 @ X4 @ X5)
% 0.21/0.51          | (v2_tex_2 @ X4 @ X5)
% 0.21/0.51          | ~ (l1_pre_topc @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.21/0.51        | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.51  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((~ (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.51         | (v1_tdlat_3 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38', '39', '45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '33'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2)))
% 0.21/0.51         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['1'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['1'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t23_tdlat_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.51         ( ![B:$i]:
% 0.21/0.51           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (v3_tdlat_3 @ X7)
% 0.21/0.51          | ~ (v3_pre_topc @ X8 @ X7)
% 0.21/0.51          | (v4_pre_topc @ X8 @ X7)
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.51          | ~ (l1_pre_topc @ X7)
% 0.21/0.51          | ~ (v2_pre_topc @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.51        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.51        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('62', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['56', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.21/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.21/0.51         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['55', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X12 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X12)
% 0.21/0.51          | ~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v1_tdlat_3 @ X12)
% 0.21/0.51          | ~ (v2_tex_2 @ (u1_struct_0 @ X12) @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (((~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.51         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.51         | (v1_tdlat_3 @ sk_A)
% 0.21/0.51         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['55', '66'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['55', '66'])).
% 0.21/0.51  thf('72', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.51  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((~ (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.51         | (v1_tdlat_3 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['55', '66'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2)))
% 0.21/0.51         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      ((((v1_tdlat_3 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t49_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.51             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | ~ (v3_tex_2 @ X15 @ X16)
% 0.21/0.51          | ~ (v1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.51          | ~ (l1_pre_topc @ X16)
% 0.21/0.51          | ~ (v1_tdlat_3 @ X16)
% 0.21/0.51          | ~ (v2_pre_topc @ X16)
% 0.21/0.51          | (v2_struct_0 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t49_tex_2])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.51  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('84', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('85', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('86', plain, (((v2_struct_0 @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.21/0.51  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('88', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['78', '88'])).
% 0.21/0.51  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('91', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['1'])).
% 0.21/0.51  thf('93', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['50', '93'])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      ((((v1_tdlat_3 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '94'])).
% 0.21/0.51  thf('96', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('97', plain, (((v1_tdlat_3 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['95', '96'])).
% 0.21/0.51  thf('98', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('99', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.51  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
