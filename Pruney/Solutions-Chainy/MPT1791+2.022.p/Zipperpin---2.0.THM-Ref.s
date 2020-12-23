%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4wJy4AHuJz

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:48 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 227 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          : 1009 (3280 expanded)
%              Number of equality atoms :   42 ( 134 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('46',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ X11 @ X12 )
      | ( X11 != X9 )
      | ~ ( m1_pre_topc @ X12 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X12 @ X10 )
      | ( v3_pre_topc @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('59',plain,
    ( ( m1_pre_topc @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('60',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','51'])).

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

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( X23 != X21 )
      | ( v3_pre_topc @ X23 @ ( k6_tmap_1 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X21 ) ) ) )
      | ( v3_pre_topc @ X21 @ ( k6_tmap_1 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','70'])).

thf('72',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4wJy4AHuJz
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 147 iterations in 0.093s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.37/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(t106_tmap_1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.37/0.56             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.56               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56              ( ( v3_pre_topc @ B @ A ) <=>
% 0.37/0.56                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.56                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (~
% 0.37/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.56       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d5_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.37/0.56             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ X1)
% 0.37/0.56          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.37/0.56          | ~ (l1_pre_topc @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.37/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.37/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.37/0.56         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t103_tmap_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.37/0.56             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | ~ (r2_hidden @ X17 @ (u1_pre_topc @ X18))
% 0.37/0.56          | ((u1_pre_topc @ X18) = (k5_tmap_1 @ X18 @ X17))
% 0.37/0.56          | ~ (l1_pre_topc @ X18)
% 0.37/0.56          | ~ (v2_pre_topc @ X18)
% 0.37/0.56          | (v2_struct_0 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.37/0.56  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.37/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d9_tmap_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( k6_tmap_1 @ A @ B ) =
% 0.37/0.56             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.56          | ((k6_tmap_1 @ X14 @ X13)
% 0.37/0.56              = (g1_pre_topc @ (u1_struct_0 @ X14) @ (k5_tmap_1 @ X14 @ X13)))
% 0.37/0.56          | ~ (l1_pre_topc @ X14)
% 0.37/0.56          | ~ (v2_pre_topc @ X14)
% 0.37/0.56          | (v2_struct_0 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.37/0.56            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.37/0.56            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.37/0.56  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.37/0.56         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('clc', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.37/0.56          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.37/0.56         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['18', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.37/0.56             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.56       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.56       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf(t2_tsep_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.56  thf(t65_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( l1_pre_topc @ B ) =>
% 0.37/0.56           ( ( m1_pre_topc @ A @ B ) <=>
% 0.37/0.56             ( m1_pre_topc @
% 0.37/0.56               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X7)
% 0.37/0.56          | ~ (m1_pre_topc @ X8 @ X7)
% 0.37/0.56          | (m1_pre_topc @ X8 @ 
% 0.37/0.56             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.37/0.56          | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | (m1_pre_topc @ X0 @ 
% 0.37/0.56             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_pre_topc @ X0 @ 
% 0.37/0.56           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      ((((m1_pre_topc @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56         | ~ (l1_pre_topc @ sk_A)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['32', '36'])).
% 0.37/0.56  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (((m1_pre_topc @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t39_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.56               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X4 @ X5)
% 0.37/0.56          | (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.37/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.37/0.56          | ~ (l1_pre_topc @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X0)
% 0.37/0.56          | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.56          | ~ (m1_pre_topc @ sk_A @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      ((((m1_subset_1 @ sk_B @ 
% 0.37/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.37/0.56         | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_k6_tmap_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56         ( l1_pre_topc @ A ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.37/0.56         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.37/0.56         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X15)
% 0.37/0.56          | ~ (v2_pre_topc @ X15)
% 0.37/0.56          | (v2_struct_0 @ X15)
% 0.37/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.56          | (l1_pre_topc @ (k6_tmap_1 @ X15 @ X16)))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.56  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.37/0.56  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('51', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (((m1_subset_1 @ sk_B @ 
% 0.37/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['43', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t33_tops_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.37/0.56               ( ( v3_pre_topc @ B @ A ) =>
% 0.37/0.56                 ( ![D:$i]:
% 0.37/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.37/0.56                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.56          | ~ (v3_pre_topc @ X9 @ X10)
% 0.37/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | (v3_pre_topc @ X11 @ X12)
% 0.37/0.56          | ((X11) != (X9))
% 0.37/0.56          | ~ (m1_pre_topc @ X12 @ X10)
% 0.37/0.56          | ~ (l1_pre_topc @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X10)
% 0.37/0.56          | ~ (m1_pre_topc @ X12 @ X10)
% 0.37/0.56          | (v3_pre_topc @ X9 @ X12)
% 0.37/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | ~ (v3_pre_topc @ X9 @ X10)
% 0.37/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.56          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.37/0.56          | (v3_pre_topc @ sk_B @ sk_A)
% 0.37/0.56          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['53', '55'])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56         | ~ (m1_pre_topc @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56         | (v3_pre_topc @ sk_B @ sk_A)
% 0.37/0.56         | ~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '56'])).
% 0.37/0.56  thf('58', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (((m1_pre_topc @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      ((((v3_pre_topc @ sk_B @ sk_A)
% 0.37/0.56         | ~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((m1_subset_1 @ sk_B @ 
% 0.37/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['43', '51'])).
% 0.37/0.56  thf(t105_tmap_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @
% 0.37/0.56                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 0.37/0.56               ( ( ( C ) = ( B ) ) =>
% 0.37/0.56                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.37/0.56          | ((X23) != (X21))
% 0.37/0.56          | (v3_pre_topc @ X23 @ (k6_tmap_1 @ X22 @ X21))
% 0.37/0.56          | ~ (m1_subset_1 @ X23 @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X22 @ X21))))
% 0.37/0.56          | ~ (l1_pre_topc @ X22)
% 0.37/0.56          | ~ (v2_pre_topc @ X22)
% 0.37/0.56          | (v2_struct_0 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [t105_tmap_1])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X22)
% 0.37/0.56          | ~ (v2_pre_topc @ X22)
% 0.37/0.56          | ~ (l1_pre_topc @ X22)
% 0.37/0.56          | ~ (m1_subset_1 @ X21 @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X22 @ X21))))
% 0.37/0.56          | (v3_pre_topc @ X21 @ (k6_tmap_1 @ X22 @ X21))
% 0.37/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56         | (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56         | (v2_struct_0 @ sk_A)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['61', '63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      ((((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56         | (v2_struct_0 @ sk_A)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.37/0.56  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      (((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('clc', [status(thm)], ['68', '69'])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (((v3_pre_topc @ sk_B @ sk_A))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['60', '70'])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (~
% 0.37/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.56       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '73'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
