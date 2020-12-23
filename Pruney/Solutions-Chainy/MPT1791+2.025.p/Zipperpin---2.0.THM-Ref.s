%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cPiznMp0YL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:49 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 215 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          : 1100 (3106 expanded)
%              Number of equality atoms :   50 ( 138 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X14 @ ( u1_pre_topc @ X15 ) )
      | ( ( u1_pre_topc @ X15 )
        = ( k5_tmap_1 @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k6_tmap_1 @ X13 @ X12 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( k5_tmap_1 @ X13 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf('32',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( m1_pre_topc @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_pre_topc @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('45',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( m1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('53',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','55'])).

thf('57',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) ) ) )
      | ( v3_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

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
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','55'])).

thf(t105_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) )
             => ( ( C = B )
               => ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X18 != X16 )
      | ( v3_pre_topc @ X18 @ ( k6_tmap_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('67',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X16 ) ) ) )
      | ( v3_pre_topc @ X16 @ ( k6_tmap_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','74'])).

thf('76',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cPiznMp0YL
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.58  % Solved by: fo/fo7.sh
% 0.35/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.58  % done 172 iterations in 0.122s
% 0.35/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.58  % SZS output start Refutation
% 0.35/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.35/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.35/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.58  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.35/0.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.35/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.58  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.35/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.35/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.58  thf(t106_tmap_1, conjecture,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.58           ( ( v3_pre_topc @ B @ A ) <=>
% 0.35/0.58             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.35/0.58               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.58    (~( ![A:$i]:
% 0.35/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.58            ( l1_pre_topc @ A ) ) =>
% 0.35/0.58          ( ![B:$i]:
% 0.35/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.58              ( ( v3_pre_topc @ B @ A ) <=>
% 0.35/0.58                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.35/0.58                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.35/0.58    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.35/0.58  thf('0', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('1', plain,
% 0.35/0.58      (~
% 0.35/0.58       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.35/0.58       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('split', [status(esa)], ['0'])).
% 0.35/0.58  thf('2', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('3', plain,
% 0.35/0.58      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.58      inference('split', [status(esa)], ['2'])).
% 0.35/0.58  thf('4', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(d5_pre_topc, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( l1_pre_topc @ A ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.58           ( ( v3_pre_topc @ B @ A ) <=>
% 0.35/0.58             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.35/0.58  thf('5', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.35/0.58          | ~ (v3_pre_topc @ X0 @ X1)
% 0.35/0.58          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.35/0.58          | ~ (l1_pre_topc @ X1))),
% 0.35/0.58      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.35/0.58  thf('6', plain,
% 0.35/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.58        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.35/0.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('8', plain,
% 0.35/0.58      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.35/0.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.58  thf('9', plain,
% 0.35/0.58      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.35/0.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['3', '8'])).
% 0.35/0.58  thf('10', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(t103_tmap_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.58           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.35/0.58             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.58  thf('11', plain,
% 0.35/0.58      (![X14 : $i, X15 : $i]:
% 0.35/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.58          | ~ (r2_hidden @ X14 @ (u1_pre_topc @ X15))
% 0.35/0.58          | ((u1_pre_topc @ X15) = (k5_tmap_1 @ X15 @ X14))
% 0.35/0.58          | ~ (l1_pre_topc @ X15)
% 0.35/0.58          | ~ (v2_pre_topc @ X15)
% 0.35/0.58          | (v2_struct_0 @ X15))),
% 0.35/0.58      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.35/0.58  thf('12', plain,
% 0.35/0.58      (((v2_struct_0 @ sk_A)
% 0.35/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.58        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.58  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('15', plain,
% 0.35/0.58      (((v2_struct_0 @ sk_A)
% 0.35/0.58        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.35/0.58      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.35/0.58  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('17', plain,
% 0.35/0.58      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.35/0.58        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.58      inference('clc', [status(thm)], ['15', '16'])).
% 0.35/0.58  thf('18', plain,
% 0.35/0.58      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['9', '17'])).
% 0.35/0.58  thf('19', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(d9_tmap_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.58           ( ( k6_tmap_1 @ A @ B ) =
% 0.35/0.58             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.58  thf('20', plain,
% 0.35/0.58      (![X12 : $i, X13 : $i]:
% 0.35/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.58          | ((k6_tmap_1 @ X13 @ X12)
% 0.35/0.58              = (g1_pre_topc @ (u1_struct_0 @ X13) @ (k5_tmap_1 @ X13 @ X12)))
% 0.35/0.58          | ~ (l1_pre_topc @ X13)
% 0.35/0.58          | ~ (v2_pre_topc @ X13)
% 0.35/0.58          | (v2_struct_0 @ X13))),
% 0.35/0.58      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.35/0.58  thf('21', plain,
% 0.35/0.58      (((v2_struct_0 @ sk_A)
% 0.35/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.58        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.35/0.58            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.58  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('24', plain,
% 0.35/0.58      (((v2_struct_0 @ sk_A)
% 0.35/0.58        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.35/0.58            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.35/0.58  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('26', plain,
% 0.35/0.58      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.35/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.58      inference('clc', [status(thm)], ['24', '25'])).
% 0.35/0.58  thf('27', plain,
% 0.35/0.58      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.35/0.58          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.35/0.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.58      inference('sup+', [status(thm)], ['18', '26'])).
% 0.35/0.58  thf('28', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= (~
% 0.35/0.58             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('split', [status(esa)], ['0'])).
% 0.35/0.58  thf('29', plain,
% 0.35/0.58      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= (~
% 0.35/0.58             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.35/0.58             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.58  thf('30', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.35/0.58       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.35/0.58  thf('31', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.35/0.58       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('split', [status(esa)], ['2'])).
% 0.35/0.58  thf('32', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('split', [status(esa)], ['2'])).
% 0.35/0.58  thf(t2_tsep_1, axiom,
% 0.35/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.35/0.58  thf('33', plain,
% 0.35/0.58      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.35/0.58      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.35/0.58  thf(t65_pre_topc, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( l1_pre_topc @ A ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( l1_pre_topc @ B ) =>
% 0.35/0.58           ( ( m1_pre_topc @ A @ B ) <=>
% 0.35/0.58             ( m1_pre_topc @
% 0.35/0.58               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.35/0.58  thf('34', plain,
% 0.35/0.58      (![X10 : $i, X11 : $i]:
% 0.35/0.58         (~ (l1_pre_topc @ X10)
% 0.35/0.58          | ~ (m1_pre_topc @ X11 @ X10)
% 0.35/0.58          | (m1_pre_topc @ X11 @ 
% 0.35/0.58             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.35/0.58          | ~ (l1_pre_topc @ X11))),
% 0.35/0.58      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.35/0.58  thf('35', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (~ (l1_pre_topc @ X0)
% 0.35/0.58          | ~ (l1_pre_topc @ X0)
% 0.35/0.58          | (m1_pre_topc @ X0 @ 
% 0.35/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.35/0.58          | ~ (l1_pre_topc @ X0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.58  thf('36', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         ((m1_pre_topc @ X0 @ 
% 0.35/0.58           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.35/0.58          | ~ (l1_pre_topc @ X0))),
% 0.35/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.35/0.58  thf('37', plain,
% 0.35/0.58      ((((m1_pre_topc @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58         | ~ (l1_pre_topc @ sk_A)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup+', [status(thm)], ['32', '36'])).
% 0.35/0.58  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('39', plain,
% 0.35/0.58      (((m1_pre_topc @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.35/0.58  thf('40', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(t39_pre_topc, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( l1_pre_topc @ A ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.35/0.58           ( ![C:$i]:
% 0.35/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.35/0.58               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.35/0.58  thf('41', plain,
% 0.35/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.58         (~ (m1_pre_topc @ X4 @ X5)
% 0.35/0.58          | (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.35/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.58          | ~ (l1_pre_topc @ X5))),
% 0.35/0.58      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.35/0.58  thf('42', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (~ (l1_pre_topc @ X0)
% 0.35/0.58          | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.58          | ~ (m1_pre_topc @ sk_A @ X0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.58  thf('43', plain,
% 0.35/0.58      ((((m1_subset_1 @ sk_B @ 
% 0.35/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.35/0.58         | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['39', '42'])).
% 0.35/0.58  thf('44', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('split', [status(esa)], ['2'])).
% 0.35/0.58  thf('45', plain,
% 0.35/0.58      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.35/0.58      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.35/0.58  thf(t11_tmap_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( l1_pre_topc @ A ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.35/0.58           ( ( v1_pre_topc @
% 0.35/0.58               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.35/0.58             ( m1_pre_topc @
% 0.35/0.58               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.35/0.58  thf('46', plain,
% 0.35/0.58      (![X19 : $i, X20 : $i]:
% 0.35/0.58         (~ (m1_pre_topc @ X19 @ X20)
% 0.35/0.58          | (m1_pre_topc @ 
% 0.35/0.58             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)) @ X20)
% 0.35/0.58          | ~ (l1_pre_topc @ X20))),
% 0.35/0.58      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.35/0.58  thf('47', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (~ (l1_pre_topc @ X0)
% 0.35/0.58          | ~ (l1_pre_topc @ X0)
% 0.35/0.58          | (m1_pre_topc @ 
% 0.35/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.58  thf('48', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         ((m1_pre_topc @ 
% 0.35/0.58           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.35/0.58          | ~ (l1_pre_topc @ X0))),
% 0.35/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.35/0.58  thf('49', plain,
% 0.35/0.58      ((((m1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 0.35/0.58         | ~ (l1_pre_topc @ sk_A)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup+', [status(thm)], ['44', '48'])).
% 0.35/0.58  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('51', plain,
% 0.35/0.58      (((m1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.35/0.58  thf(dt_m1_pre_topc, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( l1_pre_topc @ A ) =>
% 0.35/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.35/0.58  thf('52', plain,
% 0.35/0.58      (![X2 : $i, X3 : $i]:
% 0.35/0.58         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.35/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.35/0.58  thf('53', plain,
% 0.35/0.58      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.58  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('55', plain,
% 0.35/0.58      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['53', '54'])).
% 0.35/0.58  thf('56', plain,
% 0.35/0.58      (((m1_subset_1 @ sk_B @ 
% 0.35/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['43', '55'])).
% 0.35/0.58  thf('57', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('split', [status(esa)], ['2'])).
% 0.35/0.58  thf(t60_pre_topc, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.35/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.35/0.58           ( ( v3_pre_topc @
% 0.35/0.58               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.35/0.58             ( m1_subset_1 @
% 0.35/0.58               B @ 
% 0.35/0.58               ( k1_zfmisc_1 @
% 0.35/0.58                 ( u1_struct_0 @
% 0.35/0.58                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.35/0.58  thf('58', plain,
% 0.35/0.58      (![X7 : $i, X8 : $i]:
% 0.35/0.58         (~ (v3_pre_topc @ X7 @ 
% 0.35/0.58             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.35/0.58          | ~ (m1_subset_1 @ X7 @ 
% 0.35/0.58               (k1_zfmisc_1 @ 
% 0.35/0.58                (u1_struct_0 @ 
% 0.35/0.58                 (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))))
% 0.35/0.58          | (v3_pre_topc @ X7 @ X8)
% 0.35/0.58          | ~ (l1_pre_topc @ X8)
% 0.35/0.58          | ~ (v2_pre_topc @ X8))),
% 0.35/0.58      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.35/0.58  thf('59', plain,
% 0.35/0.58      ((![X0 : $i]:
% 0.35/0.58          (~ (m1_subset_1 @ X0 @ 
% 0.35/0.58              (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.35/0.58           | ~ (v2_pre_topc @ sk_A)
% 0.35/0.58           | ~ (l1_pre_topc @ sk_A)
% 0.35/0.58           | (v3_pre_topc @ X0 @ sk_A)
% 0.35/0.58           | ~ (v3_pre_topc @ X0 @ 
% 0.35/0.58                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.58  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('62', plain,
% 0.35/0.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('split', [status(esa)], ['2'])).
% 0.35/0.58  thf('63', plain,
% 0.35/0.58      ((![X0 : $i]:
% 0.35/0.58          (~ (m1_subset_1 @ X0 @ 
% 0.35/0.58              (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.35/0.58           | (v3_pre_topc @ X0 @ sk_A)
% 0.35/0.58           | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.35/0.58  thf('64', plain,
% 0.35/0.58      (((~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58         | (v3_pre_topc @ sk_B @ sk_A)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['56', '63'])).
% 0.35/0.58  thf('65', plain,
% 0.35/0.58      (((m1_subset_1 @ sk_B @ 
% 0.35/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['43', '55'])).
% 0.35/0.58  thf(t105_tmap_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.58           ( ![C:$i]:
% 0.35/0.58             ( ( m1_subset_1 @
% 0.35/0.58                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 0.35/0.58               ( ( ( C ) = ( B ) ) =>
% 0.35/0.58                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.35/0.58  thf('66', plain,
% 0.35/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.58          | ((X18) != (X16))
% 0.35/0.58          | (v3_pre_topc @ X18 @ (k6_tmap_1 @ X17 @ X16))
% 0.35/0.58          | ~ (m1_subset_1 @ X18 @ 
% 0.35/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X17 @ X16))))
% 0.35/0.58          | ~ (l1_pre_topc @ X17)
% 0.35/0.58          | ~ (v2_pre_topc @ X17)
% 0.35/0.58          | (v2_struct_0 @ X17))),
% 0.35/0.58      inference('cnf', [status(esa)], [t105_tmap_1])).
% 0.35/0.58  thf('67', plain,
% 0.35/0.58      (![X16 : $i, X17 : $i]:
% 0.35/0.58         ((v2_struct_0 @ X17)
% 0.35/0.58          | ~ (v2_pre_topc @ X17)
% 0.35/0.58          | ~ (l1_pre_topc @ X17)
% 0.35/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.35/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X17 @ X16))))
% 0.35/0.58          | (v3_pre_topc @ X16 @ (k6_tmap_1 @ X17 @ X16))
% 0.35/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.35/0.58      inference('simplify', [status(thm)], ['66'])).
% 0.35/0.58  thf('68', plain,
% 0.35/0.58      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.58         | (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.35/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.35/0.58         | (v2_struct_0 @ sk_A)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['65', '67'])).
% 0.35/0.58  thf('69', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('72', plain,
% 0.35/0.58      ((((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.35/0.58         | (v2_struct_0 @ sk_A)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.35/0.58  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('74', plain,
% 0.35/0.58      (((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('clc', [status(thm)], ['72', '73'])).
% 0.35/0.58  thf('75', plain,
% 0.35/0.58      (((v3_pre_topc @ sk_B @ sk_A))
% 0.35/0.58         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.58      inference('demod', [status(thm)], ['64', '74'])).
% 0.35/0.58  thf('76', plain,
% 0.35/0.58      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.58      inference('split', [status(esa)], ['0'])).
% 0.35/0.58  thf('77', plain,
% 0.35/0.58      (~
% 0.35/0.58       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.58          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.35/0.58       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.35/0.58  thf('78', plain, ($false),
% 0.35/0.58      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '77'])).
% 0.35/0.58  
% 0.35/0.58  % SZS output end Refutation
% 0.35/0.58  
% 0.35/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
