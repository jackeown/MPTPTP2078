%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l1c6R2hxzz

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 510 expanded)
%              Number of leaves         :   28 ( 152 expanded)
%              Depth                    :   21
%              Number of atoms          : 2179 (7765 expanded)
%              Number of equality atoms :   96 ( 328 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(t106_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k6_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X3 @ X4 )
      | ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
          <=> ( ( u1_pre_topc @ A )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_hidden @ X17 @ ( u1_pre_topc @ X18 ) )
      | ( ( u1_pre_topc @ X18 )
        = ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k6_tmap_1 @ X14 @ X13 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( k5_tmap_1 @ X14 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t32_compts_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tops_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
        <=> ( ( v1_tops_2 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_tops_2 @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_tops_2 @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ) )
      | ( v1_tops_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X19 ) )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','59','60','61','62'])).

thf('64',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X20 @ X19 ) )
        = ( k5_tmap_1 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('78',plain,
    ( ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('83',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('86',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','75','84','85','86'])).

thf('88',plain,
    ( ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','102'])).

thf('104',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,
    ( ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('108',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('109',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_tops_2 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['107','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','115'])).

thf('117',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('119',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_tops_2 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ( v1_tops_2 @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('132',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('133',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('136',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('141',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('142',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('143',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','139','140','141','142','143','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ X18 )
       != ( k5_tmap_1 @ X18 @ X17 ) )
      | ( r2_hidden @ X17 @ ( u1_pre_topc @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','157'])).

thf('159',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('162',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','164'])).

thf('166',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('167',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l1c6R2hxzz
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 174 iterations in 0.086s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.54  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.21/0.54  thf(t106_tmap_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.54               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.54                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (~
% 0.21/0.54       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.21/0.54       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d5_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.54          | ~ (v3_pre_topc @ X3 @ X4)
% 0.21/0.54          | (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.21/0.54          | ~ (l1_pre_topc @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.21/0.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t103_tmap_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.21/0.54             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.54          | ~ (r2_hidden @ X17 @ (u1_pre_topc @ X18))
% 0.21/0.54          | ((u1_pre_topc @ X18) = (k5_tmap_1 @ X18 @ X17))
% 0.21/0.54          | ~ (l1_pre_topc @ X18)
% 0.21/0.54          | ~ (v2_pre_topc @ X18)
% 0.21/0.54          | (v2_struct_0 @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.54  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.21/0.54        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d9_tmap_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( k6_tmap_1 @ A @ B ) =
% 0.21/0.54             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.54          | ((k6_tmap_1 @ X14 @ X13)
% 0.21/0.54              = (g1_pre_topc @ (u1_struct_0 @ X14) @ (k5_tmap_1 @ X14 @ X13)))
% 0.21/0.54          | ~ (l1_pre_topc @ X14)
% 0.21/0.54          | ~ (v2_pre_topc @ X14)
% 0.21/0.54          | (v2_struct_0 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.21/0.54            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.21/0.54            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.54  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.21/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.21/0.54          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['18', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.21/0.54             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.21/0.54       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.21/0.54       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf(dt_u1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( u1_pre_topc @ A ) @ 
% 0.21/0.54         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X7 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.21/0.54          | ~ (l1_pre_topc @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.54  thf(dt_g1_pre_topc, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.21/0.54         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i]:
% 0.21/0.54         ((l1_pre_topc @ (g1_pre_topc @ X5 @ X6))
% 0.21/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X7 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.21/0.54          | ~ (l1_pre_topc @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.54  thf(t78_tops_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @
% 0.21/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X8 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.21/0.54          | ~ (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.21/0.54          | (v1_tops_2 @ X8 @ X9)
% 0.21/0.54          | ~ (l1_pre_topc @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.21/0.54          | ~ (r1_tarski @ (u1_pre_topc @ X0) @ (u1_pre_topc @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('39', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_tops_2 @ (u1_pre_topc @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X7 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.21/0.54          | ~ (l1_pre_topc @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.54  thf(t32_compts_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.21/0.54             ( m1_subset_1 @
% 0.21/0.54               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.21/0.54           ( ( v1_tops_2 @
% 0.21/0.54               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.21/0.54             ( m1_subset_1 @
% 0.21/0.54               B @ 
% 0.21/0.54               ( k1_zfmisc_1 @
% 0.21/0.54                 ( k1_zfmisc_1 @
% 0.21/0.54                   ( u1_struct_0 @
% 0.21/0.54                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         (~ (v1_tops_2 @ X10 @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k1_zfmisc_1 @ 
% 0.21/0.54                 (u1_struct_0 @ 
% 0.21/0.54                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))))
% 0.21/0.54          | (m1_subset_1 @ X10 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v2_pre_topc @ X11)
% 0.21/0.54          | (v2_struct_0 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (m1_subset_1 @ 
% 0.21/0.54             (u1_pre_topc @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.54          | ~ (v1_tops_2 @ 
% 0.21/0.54               (u1_pre_topc @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.54          | (m1_subset_1 @ 
% 0.21/0.54             (u1_pre_topc @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (m1_subset_1 @ 
% 0.21/0.54             (u1_pre_topc @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.54          | ~ (l1_pre_topc @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (m1_subset_1 @ 
% 0.21/0.54             (u1_pre_topc @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | (m1_subset_1 @ 
% 0.21/0.54             (u1_pre_topc @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         (~ (v1_tops_2 @ X10 @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k1_zfmisc_1 @ 
% 0.21/0.54                 (u1_struct_0 @ 
% 0.21/0.54                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))))
% 0.21/0.54          | (v1_tops_2 @ X10 @ X11)
% 0.21/0.54          | ~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v2_pre_topc @ X11)
% 0.21/0.54          | (v2_struct_0 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X0 @ 
% 0.21/0.54              (k1_zfmisc_1 @ 
% 0.21/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.54           | (v2_struct_0 @ sk_A)
% 0.21/0.54           | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54           | (v1_tops_2 @ X0 @ sk_A)
% 0.21/0.54           | ~ (v1_tops_2 @ X0 @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t104_tmap_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.54             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.54          | ((u1_struct_0 @ (k6_tmap_1 @ X20 @ X19)) = (u1_struct_0 @ X20))
% 0.21/0.54          | ~ (l1_pre_topc @ X20)
% 0.21/0.54          | ~ (v2_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.54  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.54  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X0 @ 
% 0.21/0.54              (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54           | (v2_struct_0 @ sk_A)
% 0.21/0.54           | (v1_tops_2 @ X0 @ sk_A)
% 0.21/0.54           | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['51', '59', '60', '61', '62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54         | (v2_struct_0 @ sk_A)
% 0.21/0.54         | ~ (v1_tops_2 @ 
% 0.21/0.54              (u1_pre_topc @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54              (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54         | (v1_tops_2 @ 
% 0.21/0.54            (u1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54            sk_A)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '63'])).
% 0.21/0.54  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.54          | ((u1_pre_topc @ (k6_tmap_1 @ X20 @ X19)) = (k5_tmap_1 @ X20 @ X19))
% 0.21/0.54          | ~ (l1_pre_topc @ X20)
% 0.21/0.54          | ~ (v2_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.21/0.54  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.54      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      ((((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.54      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_tops_2 @ (u1_pre_topc @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['81', '82'])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['80', '83'])).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.54      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A)
% 0.21/0.54         | (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['64', '65', '66', '67', '75', '84', '85', '86'])).
% 0.21/0.54  thf('88', plain,
% 0.21/0.54      ((((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['87'])).
% 0.21/0.54  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('clc', [status(thm)], ['88', '89'])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k5_tmap_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54         ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( k5_tmap_1 @ A @ B ) @ 
% 0.21/0.54         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X15)
% 0.21/0.54          | ~ (v2_pre_topc @ X15)
% 0.21/0.54          | (v2_struct_0 @ X15)
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.54          | (m1_subset_1 @ (k5_tmap_1 @ X15 @ X16) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k5_tmap_1])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.54  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.21/0.54  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X8 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.21/0.54          | ~ (v1_tops_2 @ X8 @ X9)
% 0.21/0.54          | (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.21/0.54          | ~ (l1_pre_topc @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.54        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.54  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.54        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.54  thf('103', plain,
% 0.21/0.54      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['90', '102'])).
% 0.21/0.54  thf('104', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i]:
% 0.21/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('105', plain,
% 0.21/0.54      (((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.54  thf('106', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('107', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_tops_2 @ (u1_pre_topc @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf('108', plain,
% 0.21/0.54      (![X7 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.21/0.54          | ~ (l1_pre_topc @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.54  thf('109', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (v1_tops_2 @ X12 @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.21/0.54          | (m1_subset_1 @ X12 @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k1_zfmisc_1 @ 
% 0.21/0.54               (u1_struct_0 @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))))
% 0.21/0.54          | ~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v2_pre_topc @ X11)
% 0.21/0.54          | (v2_struct_0 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.21/0.54  thf('110', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k1_zfmisc_1 @ 
% 0.21/0.54               (u1_struct_0 @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.21/0.54          | ~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.54  thf('111', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.21/0.54          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k1_zfmisc_1 @ 
% 0.21/0.54               (u1_struct_0 @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['110'])).
% 0.21/0.54  thf('112', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k1_zfmisc_1 @ 
% 0.21/0.54               (u1_struct_0 @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['107', '111'])).
% 0.21/0.54  thf('113', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.54           (k1_zfmisc_1 @ 
% 0.21/0.54            (k1_zfmisc_1 @ 
% 0.21/0.54             (u1_struct_0 @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['112'])).
% 0.21/0.54  thf('114', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X8 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.21/0.54          | ~ (v1_tops_2 @ X8 @ X9)
% 0.21/0.54          | (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.21/0.54          | ~ (l1_pre_topc @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.54  thf('115', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.54          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.21/0.54             (u1_pre_topc @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 0.21/0.54          | ~ (v1_tops_2 @ (u1_pre_topc @ X0) @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.54  thf('116', plain,
% 0.21/0.54      (((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.54         | (r1_tarski @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.54            (u1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.54         | ~ (l1_pre_topc @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54         | (v2_struct_0 @ sk_A)
% 0.21/0.54         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['106', '115'])).
% 0.21/0.54  thf('117', plain,
% 0.21/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('118', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.54           (k1_zfmisc_1 @ 
% 0.21/0.54            (k1_zfmisc_1 @ 
% 0.21/0.54             (u1_struct_0 @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.39/0.54          | (v2_struct_0 @ X0)
% 0.39/0.54          | ~ (l1_pre_topc @ X0))),
% 0.39/0.54      inference('simplify', [status(thm)], ['112'])).
% 0.39/0.54  thf('119', plain,
% 0.39/0.54      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.39/0.54          (k1_zfmisc_1 @ 
% 0.39/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.39/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.54         | (v2_struct_0 @ sk_A)
% 0.39/0.54         | ~ (v2_pre_topc @ sk_A)))
% 0.39/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.54      inference('sup+', [status(thm)], ['117', '118'])).
% 0.39/0.54  thf('120', plain,
% 0.39/0.54      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.39/0.54      inference('clc', [status(thm)], ['57', '58'])).
% 0.39/0.54  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('123', plain,
% 0.39/0.54      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.39/0.54          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.54         | (v2_struct_0 @ sk_A)))
% 0.39/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.54      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.39/0.54  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('125', plain,
% 0.39/0.54      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.39/0.54         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.54      inference('clc', [status(thm)], ['123', '124'])).
% 0.39/0.54  thf('126', plain,
% 0.39/0.54      (![X11 : $i, X12 : $i]:
% 0.39/0.54         (~ (v1_tops_2 @ X12 @ X11)
% 0.39/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.39/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.39/0.54          | (v1_tops_2 @ X12 @ 
% 0.39/0.54             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.39/0.54          | ~ (l1_pre_topc @ X11)
% 0.39/0.54          | ~ (v2_pre_topc @ X11)
% 0.39/0.54          | (v2_struct_0 @ X11))),
% 0.39/0.54      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.39/0.54  thf('127', plain,
% 0.39/0.54      ((((v2_struct_0 @ sk_A)
% 0.39/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.39/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.54         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ 
% 0.39/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.39/0.54         | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)))
% 0.39/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.54      inference('sup-', [status(thm)], ['125', '126'])).
% 0.39/0.54  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('130', plain,
% 0.39/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.39/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.54      inference('split', [status(esa)], ['2'])).
% 0.39/0.54  thf('131', plain,
% 0.39/0.54      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.39/0.54         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.54      inference('clc', [status(thm)], ['123', '124'])).
% 0.39/0.54  thf('132', plain,
% 0.39/0.54      (![X8 : $i, X9 : $i]:
% 0.39/0.54         (~ (m1_subset_1 @ X8 @ 
% 0.39/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.39/0.54          | ~ (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.39/0.54          | (v1_tops_2 @ X8 @ X9)
% 0.39/0.54          | ~ (l1_pre_topc @ X9))),
% 0.39/0.54      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.39/0.54  thf('133', plain,
% 0.39/0.54      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.54         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.39/0.54         | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.39/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.54                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.54      inference('sup-', [status(thm)], ['131', '132'])).
% 0.39/0.54  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('135', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.55  thf('136', plain,
% 0.39/0.55      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.39/0.55  thf('137', plain,
% 0.39/0.55      ((((v2_struct_0 @ sk_A)
% 0.39/0.55         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('demod', [status(thm)], ['127', '128', '129', '130', '136'])).
% 0.39/0.55  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('139', plain,
% 0.39/0.55      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('clc', [status(thm)], ['137', '138'])).
% 0.39/0.55  thf('140', plain,
% 0.39/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('split', [status(esa)], ['2'])).
% 0.39/0.55  thf('141', plain,
% 0.39/0.55      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.39/0.55      inference('clc', [status(thm)], ['73', '74'])).
% 0.39/0.55  thf('142', plain,
% 0.39/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('split', [status(esa)], ['2'])).
% 0.39/0.55  thf('143', plain,
% 0.39/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('demod', [status(thm)], ['78', '79'])).
% 0.39/0.55  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('146', plain,
% 0.39/0.55      ((((r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.39/0.55         | (v2_struct_0 @ sk_A)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('demod', [status(thm)],
% 0.39/0.55                ['116', '139', '140', '141', '142', '143', '144', '145'])).
% 0.39/0.55  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('148', plain,
% 0.39/0.55      (((r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('clc', [status(thm)], ['146', '147'])).
% 0.39/0.55  thf('149', plain,
% 0.39/0.55      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('demod', [status(thm)], ['105', '148'])).
% 0.39/0.55  thf('150', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('151', plain,
% 0.39/0.55      (![X17 : $i, X18 : $i]:
% 0.39/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.55          | ((u1_pre_topc @ X18) != (k5_tmap_1 @ X18 @ X17))
% 0.39/0.55          | (r2_hidden @ X17 @ (u1_pre_topc @ X18))
% 0.39/0.55          | ~ (l1_pre_topc @ X18)
% 0.39/0.55          | ~ (v2_pre_topc @ X18)
% 0.39/0.55          | (v2_struct_0 @ X18))),
% 0.39/0.55      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.39/0.55  thf('152', plain,
% 0.39/0.55      (((v2_struct_0 @ sk_A)
% 0.39/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.39/0.55        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('sup-', [status(thm)], ['150', '151'])).
% 0.39/0.55  thf('153', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('155', plain,
% 0.39/0.55      (((v2_struct_0 @ sk_A)
% 0.39/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.39/0.55        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('demod', [status(thm)], ['152', '153', '154'])).
% 0.39/0.55  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('157', plain,
% 0.39/0.55      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.39/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.39/0.55      inference('clc', [status(thm)], ['155', '156'])).
% 0.39/0.55  thf('158', plain,
% 0.39/0.55      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.39/0.55         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('sup-', [status(thm)], ['149', '157'])).
% 0.39/0.55  thf('159', plain,
% 0.39/0.55      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('simplify', [status(thm)], ['158'])).
% 0.39/0.55  thf('160', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('161', plain,
% 0.39/0.55      (![X3 : $i, X4 : $i]:
% 0.39/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.39/0.55          | ~ (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.39/0.55          | (v3_pre_topc @ X3 @ X4)
% 0.39/0.55          | ~ (l1_pre_topc @ X4))),
% 0.39/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.39/0.55  thf('162', plain,
% 0.39/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.55        | (v3_pre_topc @ sk_B @ sk_A)
% 0.39/0.55        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.39/0.55      inference('sup-', [status(thm)], ['160', '161'])).
% 0.39/0.55  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('164', plain,
% 0.39/0.55      (((v3_pre_topc @ sk_B @ sk_A)
% 0.39/0.55        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.39/0.55      inference('demod', [status(thm)], ['162', '163'])).
% 0.39/0.55  thf('165', plain,
% 0.39/0.55      (((v3_pre_topc @ sk_B @ sk_A))
% 0.39/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('sup-', [status(thm)], ['159', '164'])).
% 0.39/0.55  thf('166', plain,
% 0.39/0.55      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.55      inference('split', [status(esa)], ['0'])).
% 0.39/0.55  thf('167', plain,
% 0.39/0.55      (~
% 0.39/0.55       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.39/0.55          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.39/0.55       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.39/0.55      inference('sup-', [status(thm)], ['165', '166'])).
% 0.39/0.55  thf('168', plain, ($false),
% 0.39/0.55      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '167'])).
% 0.39/0.55  
% 0.39/0.55  % SZS output end Refutation
% 0.39/0.55  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
