%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vRLAWgsb1d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 272 expanded)
%              Number of leaves         :   23 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          : 1019 (3953 expanded)
%              Number of equality atoms :   59 ( 188 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ( ( u1_pre_topc @ X12 )
        = ( k5_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X14 @ X13 ) )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
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
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X9 @ X10 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X9 @ X10 ) ) ) ),
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
    = ( g1_pre_topc @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X14 @ X13 ) )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
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

thf('60',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('69',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ( ( k6_tmap_1 @ sk_A @ sk_B )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ sk_B )
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( ( k5_tmap_1 @ sk_A @ sk_B )
        = ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','72'])).

thf('74',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( u1_pre_topc @ X12 )
       != ( k5_tmap_1 @ X12 @ X11 ) )
      | ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ( v3_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vRLAWgsb1d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 74 iterations in 0.023s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.20/0.46  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.46  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.46  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.20/0.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.46  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(t106_tmap_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.46             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.46               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.46            ( l1_pre_topc @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46              ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.46                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.46                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.46       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d5_pre_topc, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_pre_topc @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.46             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.46          | ~ (v3_pre_topc @ X1 @ X2)
% 0.20/0.46          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.20/0.46          | ~ (l1_pre_topc @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.46        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.46        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.20/0.46         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t103_tmap_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.20/0.46             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.46          | ~ (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 0.20/0.46          | ((u1_pre_topc @ X12) = (k5_tmap_1 @ X12 @ X11))
% 0.20/0.46          | ~ (l1_pre_topc @ X12)
% 0.20/0.46          | ~ (v2_pre_topc @ X12)
% 0.20/0.46          | (v2_struct_0 @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.46  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.46        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t104_tmap_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.46             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.46          | ((u1_pre_topc @ (k6_tmap_1 @ X14 @ X13)) = (k5_tmap_1 @ X14 @ X13))
% 0.20/0.46          | ~ (l1_pre_topc @ X14)
% 0.20/0.46          | ~ (v2_pre_topc @ X14)
% 0.20/0.46          | (v2_struct_0 @ X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.46  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_pre_topc @ A ) =>
% 0.20/0.46       ( ( v1_pre_topc @ A ) =>
% 0.20/0.46         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_pre_topc @ X0)
% 0.20/0.46          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.46          | ~ (l1_pre_topc @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.20/0.46          = (g1_pre_topc @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.20/0.46             (k5_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.46        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(dt_k6_tmap_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.46         ( l1_pre_topc @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.46       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.46         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.46         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X9)
% 0.20/0.46          | ~ (v2_pre_topc @ X9)
% 0.20/0.46          | (v2_struct_0 @ X9)
% 0.20/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.46          | (l1_pre_topc @ (k6_tmap_1 @ X9 @ X10)))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | (v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.20/0.46  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('36', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X9)
% 0.20/0.46          | ~ (v2_pre_topc @ X9)
% 0.20/0.46          | (v2_struct_0 @ X9)
% 0.20/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.46          | (v1_pre_topc @ (k6_tmap_1 @ X9 @ X10)))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | (v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.46  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('42', plain,
% 0.20/0.46      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.46  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('44', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.46  thf('45', plain,
% 0.20/0.46      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.20/0.46         = (g1_pre_topc @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.20/0.46            (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '36', '44'])).
% 0.20/0.46  thf('46', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('47', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.46          | ((u1_struct_0 @ (k6_tmap_1 @ X14 @ X13)) = (u1_struct_0 @ X14))
% 0.20/0.46          | ~ (l1_pre_topc @ X14)
% 0.20/0.46          | ~ (v2_pre_topc @ X14)
% 0.20/0.46          | (v2_struct_0 @ X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.46  thf('48', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.46  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('51', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.46  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('53', plain,
% 0.20/0.46      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.46  thf('54', plain,
% 0.20/0.46      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.20/0.46         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('demod', [status(thm)], ['45', '53'])).
% 0.20/0.46  thf('55', plain,
% 0.20/0.46      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.20/0.46          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.46         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['18', '54'])).
% 0.20/0.46  thf('56', plain,
% 0.20/0.46      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('57', plain,
% 0.20/0.46      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.20/0.46             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.46  thf('58', plain,
% 0.20/0.46      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.46       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.46  thf('59', plain,
% 0.20/0.46      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.46       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf('60', plain,
% 0.20/0.46      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf('61', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(dt_k5_tmap_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.46         ( l1_pre_topc @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.46       ( m1_subset_1 @
% 0.20/0.46         ( k5_tmap_1 @ A @ B ) @ 
% 0.20/0.46         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.46  thf('62', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X7)
% 0.20/0.46          | ~ (v2_pre_topc @ X7)
% 0.20/0.46          | (v2_struct_0 @ X7)
% 0.20/0.46          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.46          | (m1_subset_1 @ (k5_tmap_1 @ X7 @ X8) @ 
% 0.20/0.46             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k5_tmap_1])).
% 0.20/0.46  thf('63', plain,
% 0.20/0.46      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.20/0.46         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.46        | (v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.46  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('66', plain,
% 0.20/0.46      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.20/0.46         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.46        | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.46  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('68', plain,
% 0.20/0.46      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.46      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.46  thf(free_g1_pre_topc, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46       ( ![C:$i,D:$i]:
% 0.20/0.46         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.46           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.46  thf('69', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.46         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.20/0.46          | ((X6) = (X4))
% 0.20/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.46      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.46  thf('70', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((k5_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.20/0.46          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46              != (g1_pre_topc @ X1 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.46  thf('71', plain,
% 0.20/0.46      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.20/0.46         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('demod', [status(thm)], ['45', '53'])).
% 0.20/0.46  thf('72', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((k5_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.20/0.46          | ((k6_tmap_1 @ sk_A @ sk_B) != (g1_pre_topc @ X1 @ X0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.46  thf('73', plain,
% 0.20/0.46      (((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46         | ((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ sk_A))))
% 0.20/0.46         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['60', '72'])).
% 0.20/0.46  thf('74', plain,
% 0.20/0.46      ((((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ sk_A)))
% 0.20/0.46         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.46  thf('75', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('76', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.46          | ((u1_pre_topc @ X12) != (k5_tmap_1 @ X12 @ X11))
% 0.20/0.46          | (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 0.20/0.46          | ~ (l1_pre_topc @ X12)
% 0.20/0.46          | ~ (v2_pre_topc @ X12)
% 0.20/0.46          | (v2_struct_0 @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.20/0.46  thf('77', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.46        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.46  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('80', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.46        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.20/0.46  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('82', plain,
% 0.20/0.46      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.20/0.46        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.46      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.46  thf('83', plain,
% 0.20/0.46      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.20/0.46         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.20/0.46         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['74', '82'])).
% 0.20/0.46  thf('84', plain,
% 0.20/0.46      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.20/0.46         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.46  thf('85', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('86', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.46          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.20/0.46          | (v3_pre_topc @ X1 @ X2)
% 0.20/0.46          | ~ (l1_pre_topc @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.46  thf('87', plain,
% 0.20/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | (v3_pre_topc @ sk_B @ sk_A)
% 0.20/0.46        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.46  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('89', plain,
% 0.20/0.46      (((v3_pre_topc @ sk_B @ sk_A)
% 0.20/0.46        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.46  thf('90', plain,
% 0.20/0.46      (((v3_pre_topc @ sk_B @ sk_A))
% 0.20/0.46         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['84', '89'])).
% 0.20/0.46  thf('91', plain,
% 0.20/0.46      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('92', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.46          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.46       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.46  thf('93', plain, ($false),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '92'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
