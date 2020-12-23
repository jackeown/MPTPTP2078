%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0N46tV9ae

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:46 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  221 (1255 expanded)
%              Number of leaves         :   29 ( 376 expanded)
%              Depth                    :   33
%              Number of atoms          : 1719 (16760 expanded)
%              Number of equality atoms :   83 ( 717 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X3 )
      | ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ( ( u1_pre_topc @ X17 )
        = ( k5_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X18 ) )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('28',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('31',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('39',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X19 @ X18 ) )
        = ( k5_tmap_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','54'])).

thf('56',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('63',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('65',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','66'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('69',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('71',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('72',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X19 @ X18 ) )
        = ( k5_tmap_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ( ( u1_pre_topc @ X17 )
        = ( k5_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('88',plain,(
    ! [X8: $i] :
      ( ( ( k1_tops_1 @ X8 @ ( k2_struct_0 @ X8 ) )
        = ( k2_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('89',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X3 )
      | ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ( v3_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('107',plain,
    ( ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('112',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['87','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('115',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('117',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('120',plain,(
    r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('128',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('131',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X18 ) )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['129','137'])).

thf('139',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('140',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('143',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('144',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['141','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('152',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('155',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('156',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['153','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('164',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','140','152','164'])).

thf('166',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('167',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('169',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('171',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_pre_topc @ X17 )
       != ( k5_tmap_1 @ X17 @ X16 ) )
      | ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','179'])).

thf('181',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ( v3_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('184',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['181','186'])).

thf('188',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('189',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0N46tV9ae
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:31:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 229 iterations in 0.181s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.65  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.65  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.45/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.65  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.65  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.45/0.65  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(t106_tmap_1, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.65             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.65               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65            ( l1_pre_topc @ A ) ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65              ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.65                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.65                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (~
% 0.45/0.65       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.65       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['2'])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d5_pre_topc, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_pre_topc @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.65             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.45/0.65          | ~ (v3_pre_topc @ X2 @ X3)
% 0.45/0.65          | (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.45/0.65          | ~ (l1_pre_topc @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.45/0.65         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['3', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t103_tmap_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.45/0.65             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.65          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.45/0.65          | ((u1_pre_topc @ X17) = (k5_tmap_1 @ X17 @ X16))
% 0.45/0.65          | ~ (l1_pre_topc @ X17)
% 0.45/0.65          | ~ (v2_pre_topc @ X17)
% 0.45/0.65          | (v2_struct_0 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.65  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t104_tmap_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.45/0.65             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | ((u1_struct_0 @ (k6_tmap_1 @ X19 @ X18)) = (u1_struct_0 @ X19))
% 0.45/0.65          | ~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.65  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.65  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf(abstractness_v1_pre_topc, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_pre_topc @ A ) =>
% 0.45/0.65       ( ( v1_pre_topc @ A ) =>
% 0.45/0.65         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_pre_topc @ X0)
% 0.45/0.65          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.65          | ~ (l1_pre_topc @ X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.65          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.45/0.65        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_k6_tmap_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65         ( l1_pre_topc @ A ) & 
% 0.45/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.65         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.65         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X14)
% 0.45/0.65          | ~ (v2_pre_topc @ X14)
% 0.45/0.65          | (v2_struct_0 @ X14)
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.65          | (l1_pre_topc @ (k6_tmap_1 @ X14 @ X15)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.45/0.65  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('36', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X14)
% 0.45/0.65          | ~ (v2_pre_topc @ X14)
% 0.45/0.65          | (v2_struct_0 @ X14)
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.65          | (v1_pre_topc @ (k6_tmap_1 @ X14 @ X15)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.45/0.65  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('44', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.65         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '36', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | ((u1_pre_topc @ (k6_tmap_1 @ X19 @ X18)) = (k5_tmap_1 @ X19 @ X18))
% 0.45/0.65          | ~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.45/0.65  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.65         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['45', '53'])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.65          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.45/0.65         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['18', '54'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= (~
% 0.45/0.65             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= (~
% 0.45/0.65             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.45/0.65             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.65       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('simplify', [status(thm)], ['57'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.65       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('split', [status(esa)], ['2'])).
% 0.45/0.65  thf(d3_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['61', '62'])).
% 0.45/0.65  thf('64', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf(dt_l1_pre_topc, axiom,
% 0.45/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.65  thf('65', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.65  thf('66', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['63', '66'])).
% 0.45/0.65  thf(dt_k2_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_struct_0 @ A ) =>
% 0.45/0.65       ( m1_subset_1 @
% 0.45/0.65         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.45/0.65          | ~ (l1_struct_0 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.45/0.65        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['67', '68'])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf('71', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['60', '72'])).
% 0.45/0.65  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('75', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.65  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['73', '76'])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | ((u1_pre_topc @ (k6_tmap_1 @ X19 @ X18)) = (k5_tmap_1 @ X19 @ X18))
% 0.45/0.65          | ~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65            = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.65  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('82', plain,
% 0.45/0.65      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['73', '76'])).
% 0.45/0.65  thf('83', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.65          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.45/0.65          | ((u1_pre_topc @ X17) = (k5_tmap_1 @ X17 @ X16))
% 0.45/0.65          | ~ (l1_pre_topc @ X17)
% 0.45/0.65          | ~ (v2_pre_topc @ X17)
% 0.45/0.65          | (v2_struct_0 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.65  thf('84', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65        | ~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.65  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('87', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(t43_tops_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.45/0.65  thf('88', plain,
% 0.45/0.65      (![X8 : $i]:
% 0.45/0.65         (((k1_tops_1 @ X8 @ (k2_struct_0 @ X8)) = (k2_struct_0 @ X8))
% 0.45/0.65          | ~ (l1_pre_topc @ X8)
% 0.45/0.65          | ~ (v2_pre_topc @ X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.45/0.65          | ~ (l1_struct_0 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.45/0.65  thf(fc9_tops_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.45/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.45/0.65  thf('90', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X6)
% 0.45/0.65          | ~ (v2_pre_topc @ X6)
% 0.45/0.65          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.45/0.65          | (v3_pre_topc @ (k1_tops_1 @ X6 @ X7) @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.45/0.65  thf('91', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (l1_struct_0 @ X0)
% 0.45/0.65          | (v3_pre_topc @ (k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.65  thf('92', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_struct_0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['88', '91'])).
% 0.45/0.65  thf('93', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (l1_struct_0 @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | (v3_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['92'])).
% 0.45/0.65  thf('94', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.45/0.65          | ~ (l1_struct_0 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.45/0.65  thf('95', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.45/0.65          | ~ (v3_pre_topc @ X2 @ X3)
% 0.45/0.65          | (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.45/0.65          | ~ (l1_pre_topc @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.65  thf('96', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (l1_struct_0 @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | (r2_hidden @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.45/0.65          | ~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.65  thf('97', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_struct_0 @ X0)
% 0.45/0.65          | (r2_hidden @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_struct_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['93', '96'])).
% 0.45/0.65  thf('98', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.45/0.65          | ~ (l1_struct_0 @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['97'])).
% 0.45/0.65  thf('99', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('100', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.45/0.65  thf('101', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.45/0.65          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.45/0.65          | (v3_pre_topc @ X2 @ X3)
% 0.45/0.65          | ~ (l1_pre_topc @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.65  thf('102', plain,
% 0.45/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['100', '101'])).
% 0.45/0.65  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('104', plain,
% 0.45/0.65      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.65  thf('105', plain,
% 0.45/0.65      ((~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['99', '104'])).
% 0.45/0.65  thf('106', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('107', plain,
% 0.45/0.65      ((~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['105', '106'])).
% 0.45/0.65  thf('108', plain,
% 0.45/0.65      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['98', '107'])).
% 0.45/0.65  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('112', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.45/0.65  thf('113', plain,
% 0.45/0.65      (((v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['87', '112'])).
% 0.45/0.65  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('115', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['113', '114'])).
% 0.45/0.65  thf('116', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (l1_struct_0 @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | (r2_hidden @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.45/0.65          | ~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.65  thf('117', plain,
% 0.45/0.65      (((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['115', '116'])).
% 0.45/0.65  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('120', plain,
% 0.45/0.65      ((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.45/0.65  thf('121', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['84', '85', '86', '120'])).
% 0.45/0.65  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('123', plain,
% 0.45/0.65      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['121', '122'])).
% 0.45/0.65  thf('124', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65            = (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['79', '80', '81', '123'])).
% 0.45/0.65  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('126', plain,
% 0.45/0.65      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65         = (u1_pre_topc @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['124', '125'])).
% 0.45/0.65  thf('127', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_pre_topc @ X0)
% 0.45/0.65          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.65          | ~ (l1_pre_topc @ X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.45/0.65  thf('128', plain,
% 0.45/0.65      ((((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.45/0.65          = (g1_pre_topc @ 
% 0.45/0.65             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.45/0.65             (u1_pre_topc @ sk_A)))
% 0.45/0.65        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['126', '127'])).
% 0.45/0.65  thf('129', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('130', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.45/0.65  thf('131', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | ((u1_struct_0 @ (k6_tmap_1 @ X19 @ X18)) = (u1_struct_0 @ X19))
% 0.45/0.65          | ~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.65  thf('132', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.65            = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['130', '131'])).
% 0.45/0.65  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('135', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.65            = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.45/0.65  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('137', plain,
% 0.45/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.65         = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['135', '136'])).
% 0.45/0.65  thf('138', plain,
% 0.45/0.65      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65          = (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['129', '137'])).
% 0.45/0.65  thf('139', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('140', plain,
% 0.45/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65         = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.65  thf('141', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('142', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.45/0.65  thf('143', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X14)
% 0.45/0.65          | ~ (v2_pre_topc @ X14)
% 0.45/0.65          | (v2_struct_0 @ X14)
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.65          | (l1_pre_topc @ (k6_tmap_1 @ X14 @ X15)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.65  thf('144', plain,
% 0.45/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['142', '143'])).
% 0.45/0.65  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('147', plain,
% 0.45/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.45/0.65  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('149', plain,
% 0.45/0.65      ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['147', '148'])).
% 0.45/0.65  thf('150', plain,
% 0.45/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['141', '149'])).
% 0.45/0.65  thf('151', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('152', plain,
% 0.45/0.65      ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['150', '151'])).
% 0.45/0.65  thf('153', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('154', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.45/0.65  thf('155', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X14)
% 0.45/0.65          | ~ (v2_pre_topc @ X14)
% 0.45/0.65          | (v2_struct_0 @ X14)
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.65          | (v1_pre_topc @ (k6_tmap_1 @ X14 @ X15)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.65  thf('156', plain,
% 0.45/0.65      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['154', '155'])).
% 0.45/0.65  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('159', plain,
% 0.45/0.65      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.45/0.65  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('161', plain,
% 0.45/0.65      ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['159', '160'])).
% 0.45/0.65  thf('162', plain,
% 0.45/0.65      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['153', '161'])).
% 0.45/0.65  thf('163', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('164', plain,
% 0.45/0.65      ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['162', '163'])).
% 0.45/0.65  thf('165', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.45/0.65         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['128', '140', '152', '164'])).
% 0.45/0.65  thf('166', plain,
% 0.45/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('split', [status(esa)], ['2'])).
% 0.45/0.65  thf('167', plain,
% 0.45/0.65      ((((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['165', '166'])).
% 0.45/0.65  thf('168', plain,
% 0.45/0.65      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.45/0.65         = (u1_pre_topc @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['124', '125'])).
% 0.45/0.65  thf('169', plain,
% 0.45/0.65      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A)))
% 0.45/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['167', '168'])).
% 0.45/0.65  thf('170', plain,
% 0.45/0.65      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('171', plain,
% 0.45/0.65      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['169', '170'])).
% 0.45/0.65  thf('172', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('173', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.65          | ((u1_pre_topc @ X17) != (k5_tmap_1 @ X17 @ X16))
% 0.45/0.65          | (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.45/0.65          | ~ (l1_pre_topc @ X17)
% 0.45/0.65          | ~ (v2_pre_topc @ X17)
% 0.45/0.65          | (v2_struct_0 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.65  thf('174', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['172', '173'])).
% 0.45/0.65  thf('175', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('177', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.65        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['174', '175', '176'])).
% 0.45/0.65  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('179', plain,
% 0.45/0.65      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['177', '178'])).
% 0.45/0.65  thf('180', plain,
% 0.45/0.65      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.45/0.65         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.45/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['171', '179'])).
% 0.45/0.65  thf('181', plain,
% 0.45/0.65      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.45/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['180'])).
% 0.45/0.65  thf('182', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('183', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.45/0.65          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.45/0.65          | (v3_pre_topc @ X2 @ X3)
% 0.45/0.65          | ~ (l1_pre_topc @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.65  thf('184', plain,
% 0.45/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ sk_B @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['182', '183'])).
% 0.45/0.65  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('186', plain,
% 0.45/0.65      (((v3_pre_topc @ sk_B @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['184', '185'])).
% 0.45/0.65  thf('187', plain,
% 0.45/0.65      (((v3_pre_topc @ sk_B @ sk_A))
% 0.45/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['181', '186'])).
% 0.45/0.65  thf('188', plain,
% 0.45/0.65      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('189', plain,
% 0.45/0.65      (~
% 0.45/0.65       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.65          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.65       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['187', '188'])).
% 0.45/0.65  thf('190', plain, ($false),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '189'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
