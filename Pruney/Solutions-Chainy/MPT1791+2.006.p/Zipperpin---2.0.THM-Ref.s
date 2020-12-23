%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7DCet1plj1

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:45 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  218 (1228 expanded)
%              Number of leaves         :   27 ( 366 expanded)
%              Depth                    :   30
%              Number of atoms          : 1895 (16930 expanded)
%              Number of equality atoms :   84 ( 707 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X16 ) )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X12 @ X13 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X12 @ X13 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X17 @ X16 ) )
        = ( k5_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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

thf('61',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('64',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','65'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('68',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('70',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('71',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X17 @ X16 ) )
        = ( k5_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X3 )
      | ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('84',plain,(
    ! [X6: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X6 ) @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('85',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X3 )
      | ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ( v3_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('99',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('101',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('105',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['83','105'])).

thf('107',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('108',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X16 ) )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('111',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( l1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( l1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('117',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X14 @ ( u1_pre_topc @ X15 ) )
      | ( ( u1_pre_topc @ X15 )
        = ( k5_tmap_1 @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['78','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('139',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('141',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X16 ) )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('149',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('150',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('157',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('158',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','147','155','163'])).

thf('165',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('166',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['78','136'])).

thf('168',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('170',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( u1_pre_topc @ X15 )
       != ( k5_tmap_1 @ X15 @ X14 ) )
      | ( r2_hidden @ X14 @ ( u1_pre_topc @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','178'])).

thf('180',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ( v3_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('183',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','185'])).

thf('187',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('188',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7DCet1plj1
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 256 iterations in 0.157s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.61  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.61  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.41/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.61  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.41/0.61  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.41/0.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.41/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(t106_tmap_1, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( v3_pre_topc @ B @ A ) <=>
% 0.43/0.61             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.43/0.61               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.61            ( l1_pre_topc @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61              ( ( v3_pre_topc @ B @ A ) <=>
% 0.43/0.61                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.43/0.61                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (~
% 0.43/0.61       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.43/0.61       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['2'])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d5_pre_topc, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_pre_topc @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( v3_pre_topc @ B @ A ) <=>
% 0.43/0.61             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.43/0.61          | ~ (v3_pre_topc @ X2 @ X3)
% 0.43/0.61          | (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.43/0.61          | ~ (l1_pre_topc @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.43/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t103_tmap_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.43/0.61             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.43/0.61          | ~ (r2_hidden @ X14 @ (u1_pre_topc @ X15))
% 0.43/0.61          | ((u1_pre_topc @ X15) = (k5_tmap_1 @ X15 @ X14))
% 0.43/0.61          | ~ (l1_pre_topc @ X15)
% 0.43/0.61          | ~ (v2_pre_topc @ X15)
% 0.43/0.61          | (v2_struct_0 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.43/0.61  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('clc', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.43/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['9', '17'])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t104_tmap_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.43/0.61             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.43/0.61          | ((u1_struct_0 @ (k6_tmap_1 @ X17 @ X16)) = (u1_struct_0 @ X17))
% 0.43/0.61          | ~ (l1_pre_topc @ X17)
% 0.43/0.61          | ~ (v2_pre_topc @ X17)
% 0.43/0.61          | (v2_struct_0 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.61  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.43/0.61  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf(abstractness_v1_pre_topc, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_pre_topc @ A ) =>
% 0.43/0.61       ( ( v1_pre_topc @ A ) =>
% 0.43/0.61         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_pre_topc @ X0)
% 0.43/0.61          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.43/0.61          | ~ (l1_pre_topc @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.43/0.61          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.43/0.61        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(dt_k6_tmap_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.61         ( l1_pre_topc @ A ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.43/0.61         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.43/0.61         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12)
% 0.43/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (l1_pre_topc @ (k6_tmap_1 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.43/0.61  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('36', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('clc', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12)
% 0.43/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (v1_pre_topc @ (k6_tmap_1 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.43/0.61  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('44', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('clc', [status(thm)], ['42', '43'])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.43/0.61         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('demod', [status(thm)], ['28', '36', '44'])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.43/0.61          | ((u1_pre_topc @ (k6_tmap_1 @ X17 @ X16)) = (k5_tmap_1 @ X17 @ X16))
% 0.43/0.61          | ~ (l1_pre_topc @ X17)
% 0.43/0.61          | ~ (v2_pre_topc @ X17)
% 0.43/0.61          | (v2_struct_0 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.61  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.43/0.61  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('clc', [status(thm)], ['51', '52'])).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.43/0.61         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('demod', [status(thm)], ['45', '53'])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.43/0.61          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.43/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['18', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.43/0.61             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.43/0.61       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['57'])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.43/0.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('split', [status(esa)], ['2'])).
% 0.43/0.61  thf(d3_struct_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (![X1 : $i]:
% 0.43/0.61         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.43/0.61        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf('63', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('clc', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf(dt_l1_pre_topc, axiom,
% 0.43/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.43/0.61  thf('64', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.61  thf('65', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['62', '65'])).
% 0.43/0.61  thf(dt_k2_struct_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_struct_0 @ A ) =>
% 0.43/0.61       ( m1_subset_1 @
% 0.43/0.61         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      (![X4 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.43/0.61          | ~ (l1_struct_0 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.43/0.61  thf('68', plain,
% 0.43/0.61      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.43/0.61        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['66', '67'])).
% 0.43/0.61  thf('69', plain,
% 0.43/0.61      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf('70', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.43/0.61  thf('72', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.43/0.61          | ((u1_pre_topc @ (k6_tmap_1 @ X17 @ X16)) = (k5_tmap_1 @ X17 @ X16))
% 0.43/0.61          | ~ (l1_pre_topc @ X17)
% 0.43/0.61          | ~ (v2_pre_topc @ X17)
% 0.43/0.61          | (v2_struct_0 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.43/0.61  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('76', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.43/0.61  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('78', plain,
% 0.43/0.61      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['76', '77'])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.43/0.61          | ~ (v3_pre_topc @ X2 @ X3)
% 0.43/0.61          | (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.43/0.61          | ~ (l1_pre_topc @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.61  thf('81', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['79', '80'])).
% 0.43/0.61  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('83', plain,
% 0.43/0.61      (((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['81', '82'])).
% 0.43/0.61  thf(fc10_tops_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.43/0.61  thf('84', plain,
% 0.43/0.61      (![X6 : $i]:
% 0.43/0.61         ((v3_pre_topc @ (k2_struct_0 @ X6) @ X6)
% 0.43/0.61          | ~ (l1_pre_topc @ X6)
% 0.43/0.61          | ~ (v2_pre_topc @ X6))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      (![X4 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.43/0.61          | ~ (l1_struct_0 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.43/0.61  thf('86', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.43/0.61          | ~ (v3_pre_topc @ X2 @ X3)
% 0.43/0.61          | (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.43/0.61          | ~ (l1_pre_topc @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.61  thf('87', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | (r2_hidden @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.43/0.61          | ~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['85', '86'])).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | (r2_hidden @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['84', '87'])).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | (r2_hidden @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['88'])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      (![X1 : $i]:
% 0.43/0.61         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.61  thf('91', plain,
% 0.43/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.43/0.61  thf('92', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.43/0.61          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.43/0.61          | (v3_pre_topc @ X2 @ X3)
% 0.43/0.61          | ~ (l1_pre_topc @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.61  thf('93', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.43/0.61  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('95', plain,
% 0.43/0.61      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['93', '94'])).
% 0.43/0.61  thf('96', plain,
% 0.43/0.61      ((~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.61        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['90', '95'])).
% 0.43/0.61  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('98', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.61  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.43/0.61  thf('100', plain,
% 0.43/0.61      ((~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['96', '99'])).
% 0.43/0.61  thf('101', plain,
% 0.43/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.61        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['89', '100'])).
% 0.43/0.61  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.43/0.61  thf('105', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.43/0.61  thf('106', plain,
% 0.43/0.61      ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['83', '105'])).
% 0.43/0.61  thf('107', plain,
% 0.43/0.61      (![X4 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.43/0.61          | ~ (l1_struct_0 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.43/0.61  thf('108', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.43/0.61          | ((u1_struct_0 @ (k6_tmap_1 @ X17 @ X16)) = (u1_struct_0 @ X17))
% 0.43/0.61          | ~ (l1_pre_topc @ X17)
% 0.43/0.61          | ~ (v2_pre_topc @ X17)
% 0.43/0.61          | (v2_struct_0 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.43/0.61  thf('109', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))
% 0.43/0.61              = (u1_struct_0 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['107', '108'])).
% 0.43/0.61  thf('110', plain,
% 0.43/0.61      (![X4 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.43/0.61          | ~ (l1_struct_0 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.43/0.61  thf('111', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12)
% 0.43/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (l1_pre_topc @ (k6_tmap_1 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.43/0.61  thf('112', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | (l1_pre_topc @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['110', '111'])).
% 0.43/0.61  thf('113', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.61  thf('114', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (l1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['112', '113'])).
% 0.43/0.61  thf('115', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (l1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['112', '113'])).
% 0.43/0.61  thf('116', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))
% 0.43/0.61              = (u1_struct_0 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['107', '108'])).
% 0.43/0.61  thf('117', plain,
% 0.43/0.61      (![X1 : $i]:
% 0.43/0.61         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.61  thf('118', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))
% 0.43/0.61            = (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['116', '117'])).
% 0.43/0.61  thf('119', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ((k2_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))
% 0.43/0.61              = (u1_struct_0 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['115', '118'])).
% 0.43/0.61  thf('120', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))
% 0.43/0.61            = (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['119'])).
% 0.43/0.61  thf('121', plain,
% 0.43/0.61      (![X4 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.43/0.61          | ~ (l1_struct_0 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.43/0.61  thf('122', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))))
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['120', '121'])).
% 0.43/0.61  thf('123', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (u1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['114', '122'])).
% 0.43/0.61  thf('124', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X0 @ (k2_struct_0 @ X0)))))
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['123'])).
% 0.43/0.61  thf('125', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['109', '124'])).
% 0.43/0.61  thf('126', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['125'])).
% 0.43/0.61  thf('127', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.43/0.61          | ~ (r2_hidden @ X14 @ (u1_pre_topc @ X15))
% 0.43/0.61          | ((u1_pre_topc @ X15) = (k5_tmap_1 @ X15 @ X14))
% 0.43/0.61          | ~ (l1_pre_topc @ X15)
% 0.43/0.61          | ~ (v2_pre_topc @ X15)
% 0.43/0.61          | (v2_struct_0 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.43/0.61  thf('128', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['126', '127'])).
% 0.43/0.61  thf('129', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.43/0.61          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (l1_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['128'])).
% 0.43/0.61  thf('130', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['106', '129'])).
% 0.43/0.61  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('133', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.43/0.61  thf('134', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.43/0.61  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('136', plain,
% 0.43/0.61      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['134', '135'])).
% 0.43/0.61  thf('137', plain,
% 0.43/0.61      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61         = (u1_pre_topc @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['78', '136'])).
% 0.43/0.61  thf('138', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_pre_topc @ X0)
% 0.43/0.61          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.43/0.61          | ~ (l1_pre_topc @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.43/0.61  thf('139', plain,
% 0.43/0.61      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.43/0.61          = (g1_pre_topc @ 
% 0.43/0.61             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))) @ 
% 0.43/0.61             (u1_pre_topc @ sk_A)))
% 0.43/0.61        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['137', '138'])).
% 0.43/0.61  thf('140', plain,
% 0.43/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.43/0.61  thf('141', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.43/0.61          | ((u1_struct_0 @ (k6_tmap_1 @ X17 @ X16)) = (u1_struct_0 @ X17))
% 0.43/0.61          | ~ (l1_pre_topc @ X17)
% 0.43/0.61          | ~ (v2_pre_topc @ X17)
% 0.43/0.61          | (v2_struct_0 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.43/0.61  thf('142', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61            = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['140', '141'])).
% 0.43/0.61  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('145', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61            = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.43/0.61  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('147', plain,
% 0.43/0.61      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61         = (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['145', '146'])).
% 0.43/0.61  thf('148', plain,
% 0.43/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.43/0.61  thf('149', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12)
% 0.43/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (l1_pre_topc @ (k6_tmap_1 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.43/0.61  thf('150', plain,
% 0.43/0.61      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['148', '149'])).
% 0.43/0.61  thf('151', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('153', plain,
% 0.43/0.61      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.43/0.61  thf('154', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('155', plain,
% 0.43/0.61      ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['153', '154'])).
% 0.43/0.61  thf('156', plain,
% 0.43/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.43/0.61  thf('157', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12)
% 0.43/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (v1_pre_topc @ (k6_tmap_1 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.43/0.61  thf('158', plain,
% 0.43/0.61      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['156', '157'])).
% 0.43/0.61  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('161', plain,
% 0.43/0.61      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.43/0.61  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('163', plain,
% 0.43/0.61      ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['161', '162'])).
% 0.43/0.61  thf('164', plain,
% 0.43/0.61      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.43/0.61         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['139', '147', '155', '163'])).
% 0.43/0.61  thf('165', plain,
% 0.43/0.61      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.43/0.61         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('split', [status(esa)], ['2'])).
% 0.43/0.61  thf('166', plain,
% 0.43/0.61      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.43/0.61         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['164', '165'])).
% 0.43/0.61  thf('167', plain,
% 0.43/0.61      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.43/0.61         = (u1_pre_topc @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['78', '136'])).
% 0.43/0.61  thf('168', plain,
% 0.43/0.61      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A)))
% 0.43/0.61         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['166', '167'])).
% 0.43/0.61  thf('169', plain,
% 0.43/0.61      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('clc', [status(thm)], ['51', '52'])).
% 0.43/0.61  thf('170', plain,
% 0.43/0.61      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.43/0.61         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['168', '169'])).
% 0.43/0.61  thf('171', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('172', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.43/0.61          | ((u1_pre_topc @ X15) != (k5_tmap_1 @ X15 @ X14))
% 0.43/0.61          | (r2_hidden @ X14 @ (u1_pre_topc @ X15))
% 0.43/0.61          | ~ (l1_pre_topc @ X15)
% 0.43/0.61          | ~ (v2_pre_topc @ X15)
% 0.43/0.61          | (v2_struct_0 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.43/0.61  thf('173', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['171', '172'])).
% 0.43/0.61  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('176', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.43/0.61        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('demod', [status(thm)], ['173', '174', '175'])).
% 0.43/0.61  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('178', plain,
% 0.43/0.61      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.43/0.61        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['176', '177'])).
% 0.43/0.61  thf('179', plain,
% 0.43/0.61      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.43/0.61         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.43/0.61         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['170', '178'])).
% 0.43/0.61  thf('180', plain,
% 0.43/0.61      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.43/0.61         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['179'])).
% 0.43/0.61  thf('181', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('182', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.43/0.61          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.43/0.61          | (v3_pre_topc @ X2 @ X3)
% 0.43/0.61          | ~ (l1_pre_topc @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.61  thf('183', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (v3_pre_topc @ sk_B @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['181', '182'])).
% 0.43/0.61  thf('184', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('185', plain,
% 0.43/0.61      (((v3_pre_topc @ sk_B @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['183', '184'])).
% 0.43/0.61  thf('186', plain,
% 0.43/0.61      (((v3_pre_topc @ sk_B @ sk_A))
% 0.43/0.61         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['180', '185'])).
% 0.43/0.61  thf('187', plain,
% 0.43/0.61      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('188', plain,
% 0.43/0.61      (~
% 0.43/0.61       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.43/0.61          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.43/0.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['186', '187'])).
% 0.43/0.61  thf('189', plain, ($false),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '188'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
